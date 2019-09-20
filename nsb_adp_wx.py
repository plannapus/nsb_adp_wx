# -*- coding: utf-8 -*-
import os, sys, subprocess
reload(sys)
sys.setdefaultencoding("utf-8")
# Basic modules
import decimal, string, datetime
import re, math
from bisect import bisect_left
import csv
# Math & DB-related modules
import numpy as np
import pandas as pd
import pandas.io.sql as psql
from sqlalchemy import create_engine
# GUI modules
import wx, wx.html
# Plot-related modules
import matplotlib
matplotlib.use('wxAgg')
import matplotlib.pyplot as plt
from matplotlib.backends.backend_wxagg import FigureCanvasWxAgg as FigureCanvas
from matplotlib.figure import Figure

# QUERY_ functions
def query_loc(engine,holeID):
    """Query LOC from database."""
    sqlRev = "SELECT c.site_hole as sh, c.revision_no as rn, current_flag, age_quality, interpreted_by, date_worked, remark FROM neptune_age_model_history as c, neptune_hole_summary as b WHERE c.site_hole=b.site_hole AND b.hole_id='%s' ORDER BY current_flag, rn DESC;" % (holeID,)
    revision_no = psql.read_sql_query(sqlRev, engine)
    if len(revision_no):
        revdial = RevisionDialog(None,revision_no)
        if revdial.ShowModal() == wx.ID_OK:
            sel = revdial.list_ctrl.GetFirstSelected()
            rev = revdial.amList[sel]
            sqlLOC = "SELECT age_ma, depth_mbsf, revision_no FROM neptune_age_model b WHERE b.site_hole = '%s' AND revision_no=%i ORDER BY age_ma, depth_mbsf;" % (rev['sh'],int(rev['rn']))
            dfLOC = psql.read_sql_query(sqlLOC, engine)
        else: dfLOC = []
    else: dfLOC = []
    return dfLOC

def query_events(engine,data): #Query events from tables in NSB Berlin database.
    sqlDATUM = """SELECT top_hole_id AS hole_id,
            event_group AS fossil_group,
            event_group AS plot_fossil_group,
            event_name AS datum_name,
            event_type AS datum_type,
            event_extent,
            plotcode AS plot_code,
            CASE
                WHEN bottom_depth_mbsf IS NOT NULL THEN
                    bottom_depth_mbsf
                WHEN sample_bottom IS NOT NULL THEN
                    neptuneCoreDepth(top_hole_id,sample_bottom)
            END AS bottom_depth,
            CASE
                WHEN top_depth_mbsf IS NOT NULL THEN
                    top_depth_mbsf
                WHEN sample_top IS NOT NULL THEN
                    neptuneCoreDepth(top_hole_id,sample_top)
            END AS top_depth,
            a.event_id AS event_id
            FROM neptune_event a, neptune_event_def c
            WHERE a.event_id = c.event_id
            AND top_hole_id = '%s';""" % (data['holeID'],)
    sqlCALIB = """SELECT event_id, calibration_scale AS scale, calibration_year, young_age_ma AS datum_age_min_ma, old_age_ma AS datum_age_max_ma
            FROM neptune_event_calibration
            WHERE (event_id,calibration_year) IN (
                SELECT DISTINCT event_id,MAX(calibration_year) AS calibration_year
                FROM neptune_event_calibration
                GROUP BY event_id)
            UNION
            SELECT event_id, scale, NULL AS calibration_year, age_ma AS datum_age_min_ma, age_ma AS datum_age_max_ma
            FROM neptune_gpts
            WHERE scale = '%s';""" % (data['toScale'],)
    datums = psql.read_sql_query(sqlDATUM, engine)
    calibs = psql.read_sql_query(sqlCALIB, engine)
    dfDATUMS = pd.merge(datums, calibs, how='left', on='event_id')
    dfDATUMS = dfDATUMS.where((pd.notnull(dfDATUMS)), None)
    for i in range(0,len(dfDATUMS)):
        if dfDATUMS['top_depth'][i] is None:
            dfDATUMS['top_depth'][i] = dfDATUMS['bottom_depth'][i]
        elif dfDATUMS['bottom_depth'][i] is None:
            dfDATUMS['bottom_depth'][i] = dfDATUMS['top_depth'][i]
        dfDATUMS['datum_name'][i] = dfDATUMS['datum_name'][i].encode('utf-8')
        if dfDATUMS['datum_age_min_ma'][i] is None:
            dfDATUMS['datum_age_min_ma'][i] = dfDATUMS['datum_age_max_ma'][i]
        if dfDATUMS['datum_age_max_ma'][i] is None:
            dfDATUMS['datum_age_max_ma'][i] = dfDATUMS['datum_age_min_ma'][i]
    return dfDATUMS

def query_cores(engine,holeID): #Work
    """Query for cores from database."""
    sqlCORE = """SELECT core,core_top_mbsf AS top_depth, (core_top_mbsf + core_length) AS bottom_depth
                 FROM neptune_core WHERE hole_id = '%s' ORDER BY top_depth;""" % (holeID,)
    dfCORES = psql.read_sql_query(sqlCORE,engine)
    dfCORES = dfCORES[dfCORES.core.str.contains('^[0-9]+$')]
    dfCORES.core = dfCORES.core.astype(int)
    dfCORES = dfCORES.sort_values('core')
    dfCORES['newIndex'] = range(0,len(dfCORES))
    dfCORES = dfCORES.set_index('newIndex')
    return dfCORES

def query_paleomag_interval(engine,holeID): #Work
    """Query for paleomag intervals from database."""
    sqlPMAG = """SELECT top_depth AS top_depth,bottom_depth AS bottom_depth,color,pattern,width
                 FROM neptune_hole_summary a, neptune_paleomag_interval b
                 WHERE a.site_hole = b.site_hole AND hole_id = '%s';""" % (holeID,)
    dfPMAGS = psql.read_sql_query(sqlPMAG,engine)
    return dfPMAGS

# FIX_ functions:
def fix_null(t,fixType):
    """Fix missing values."""
    if pd.isnull(t):
        t = None
    elif type(t) == str and t.strip() == '':
        t = None
    if fixType and t is not None:  # Ages (fixType = 1), return a float value
        return float(t)
    else:
        return t

# CALC_ functions:
def calc_core_depth(origCore,dfCORES):
    """Calculate mbsf depth for cores (core-section,int)."""
    ccFlag = 0
    origCore = origCore.strip()
    if origCore[0] == '-':
        origCore = origCore[1:]
    if origCore[0] == '?':
        origCore = origCore[1:]
    if origCore.find('(') > 0:
        origCore = origCore[0:origCore.find('(')-1]
    coreIdx = int(origCore[0:origCore.find('-')])-1
    topDepth = dfCORES['top_depth'][coreIdx]
    botDepth = dfCORES['bottom_depth'][coreIdx]
    section = origCore[origCore.find('-')+1:]
    if section[0] == 'C':  # Is this a core-catcher?
        if section.find(',') > 0:  # CC,int
            topDepth = dfCORES['bottom_depth'][coreIdx]
            section = '1'
            ccFlag = 1
        else:
            depth = dfCORES['bottom_depth'][coreIdx]  # CC but not CC,int
            return abs(depth)
    if ccFlag == 0:
        section = section[0:section.find(',')]
    interval = origCore[origCore.find(',')+1:]
    depth = topDepth + (int(section)-1) * 1.5 + .01 * float(interval)
    return abs(depth)

def calc_depth_ma(depth,x,y):
    """Calculate age from depth along LOC"""
    if depth < abs(y[0]) or depth > abs(y[len(y)-1]): # Outside of LOC range
        return None
    i = 0
    while (depth >= abs(y[i])):
        i += 1
    ma = x[i-1]
    ratio = (depth - abs(y[i-1])) / (abs(y[i]) - abs(y[i-1]))
    if ratio > 0:
        ma += ratio * (abs(x[i]) - abs(x[i-1]))

    return ma

def age_convert(age, fromScale, toScale):
    """
       Convert an age from one timescale to another.
       Based on Johan Renaudie code in AgeScaleTransform.py .
    """
    conv = []
    for i in [k['event_id'] for k in fromScale]:
        if i in [k['event_id'] for k in toScale]:
            conv.append({'event_id':i,
                         'fromScale': [k['age_ma'] for k in fromScale if k['event_id']==i][0],
                         'toScale':[k['age_ma'] for k in toScale if k['event_id']==i][0]})

    conv = sorted(conv,key=lambda x:float(x['fromScale']))
    old = map(float,[k['fromScale'] for k in conv])
    new = map(float,[k['toScale'] for k in conv])
    m = bisect_left(old, age)

    if m == 0:
        n = new[0]
    elif m == len(fromScale):
        n = new[-1]
    else:
        n = new[m-1] + (age - old[m-1])*(new[m]-new[m-1])/(old[m]-old[m-1])

    return n

# PLOT_ functions:
def get_plot_groups(dfDATUMS,plotCodes):
    """Get unique plot groups (fossilGroup and datumType) from datums dataframe
       and setup as list with [group,plot,label,highlight].
    Use plotCodes argument to set the initial label state.
    """
    plotGroups = []
    datumGroups = pd.unique(dfDATUMS['plot_fossil_group'].tolist())
    for i in range (0,len(datumGroups)):
        plotGroups.append([datumGroups[i],1,plotCodes,0,'T'])  # Top
        plotGroups.append([datumGroups[i],1,plotCodes,0,'B'])  # Base
        plotGroups.append([datumGroups[i],1,plotCodes,0,'x'])  # Other
    return plotGroups

def plot_datums(data,fig,ax,canvas):
    """Plot strat datums by fossil group (color) and top/base (symbol)."""
    dfDATUMS = data['dfDATUMS']
    plotGroups = data['plotGroups']
    plotCodes = data['plotCodes']
    # Setup lists for using with AnnoteFinder
    xdata = []
    ydata = []
    plotCodeID = []
    # Save the processed data into lists for using later
    saveGroups = []
    saveRangeGroups = []
    saveRangeBoxes = []
    # Read in config file
    configfile = os.environ['NSBPATH'] + "/REF/plot_config.txt"
    with open(configfile,'rU') as f:
        r = csv.reader(f,delimiter='\t')
        h = r.next()
        stdMarkers = []
        stdColors = []
        for row in r:
            stdMarkers.append([row[0],row[2],row[2]])
            if data['plotColorType'] == 1:
                stdColors.append([row[0],'k'])
            else:
                stdColors.append([row[0], row[3]])

    tops = ['ACME','DISP','LCO','TOP','T','Z']
    bases = ['BOT','REAP','FCO','EVOL','B']

    for i in range(0,len(dfDATUMS)):
        # Defaults for non-configured eent groups.
        marker = '*'
        color = 'k'
        lcolor = 'k'
        fillstyle = 'full'
        fossilGroup = dfDATUMS['plot_fossil_group'][i]
        datumType = dfDATUMS['datum_type'][i]
        if datumType in tops:
            datumType = 'T'
        elif datumType in bases:
            datumType = 'B'
        else: datumType = 'x'

        # Match fossilGroup with plotGroups for controls for plot,label,highlight ...
        plotGroupIdx = [ind for ind, k in enumerate(plotGroups) if k[0] == fossilGroup and k[4] == datumType][0]
        # Match datum fossil_group to stdMarkers fossil_group
        if fossilGroup in [k[0] for k in stdMarkers]:
            marker = [k[1] for k in stdMarkers if k[0]==fossilGroup][0]
            if data['plotColorType'] != 2:
                color = [k[1] for k in stdColors if k[0]==fossilGroup][0]
                lcolor = color
                fillstyle = 'top' if datumType == 'T' else 'bottom' if datumType =='B' else 'full'
            else:
                fillstyle = 'full'
                lcolor = [k[1] for k in stdColors if k[0]==fossilGroup][0]
                color = lcolor if datumType =='B' else 'white'

        # Calculate average depth and average age
        if dfDATUMS['top_depth'][i] is not None and dfDATUMS['bottom_depth'][i] is not None:
            avg_depth = (dfDATUMS['top_depth'][i] + dfDATUMS['bottom_depth'][i]) / 2.
            yHeight = abs(dfDATUMS['top_depth'][i] - dfDATUMS['bottom_depth'][i])
        else:
            avg_depth = None
            yHeight = 0
        if dfDATUMS['datum_age_max_ma'][i] is not None and dfDATUMS['datum_age_min_ma'][i] is not None:
            avg_age = (dfDATUMS['datum_age_max_ma'][i] + dfDATUMS['datum_age_min_ma'][i]) / 2.
            xWidth = dfDATUMS['datum_age_max_ma'][i] - dfDATUMS['datum_age_min_ma'][i]
        elif dfDATUMS['datum_age_max_ma'][i] is not None:
            avg_age = dfDATUMS['datum_age_max_ma'][i]
            xWidth = 0
        else:
            avg_age = dfDATUMS['datum_age_min_ma'][i]
            xWidth = 0
        # Set the markersize
        if plotGroups[plotGroupIdx][3] == 1:
            markersize = 9  # Highlight
        else:
            markersize = 7  # No highlight

        # Save data to lists for AnnoteFinder
        xdata.append(avg_age)
        ydata.append(avg_depth)
        label = dfDATUMS['plot_code'][i] + ':' + dfDATUMS['datum_name'][i]
        plotCodeID.append((dfDATUMS['plot_code'][i],dfDATUMS['datum_name'][i], lcolor))
        fd = fossilGroup+':'+datumType
        # Plot range as box
        if yHeight > 0 and xWidth > 0: saveRangeBoxes.append([plotGroupIdx, fd, dfDATUMS['datum_age_min_ma'][i], dfDATUMS['top_depth'][i], xWidth, yHeight, 'white'])
        if yHeight > 0: saveRangeGroups.append([plotGroupIdx, fd, [avg_age,avg_age], [dfDATUMS['top_depth'][i],dfDATUMS['bottom_depth'][i]], lcolor])
        if xWidth > 0: saveRangeGroups.append([plotGroupIdx, fd, [dfDATUMS['datum_age_max_ma'][i],dfDATUMS['datum_age_min_ma'][i]], [avg_depth,avg_depth], lcolor])
        # Annotate the datums with the plotCode
        # DEV: might fix this section to only use plotGroups ... either you
        # DEV: are plotting the symbol and the code, or else just the symbol ...
        if plotCodes == 1:
            # DEV: testing box around label
            #plt.annotate(dfDATUMS['plot_code'][i], xy=(avg_age + 0.1, avg_depth), size=8.,ha='left', color=lcolor, bbox=props)
            plt.annotate(dfDATUMS['plot_code'][i], xy=(avg_age + 0.1,avg_depth), size=7.,ha='left',color=lcolor)
        elif plotGroups[plotGroupIdx][2] == 1:
            plt.annotate(dfDATUMS['plot_code'][i],xy=(avg_age+0.1,avg_depth), size=7.,ha='left',color=lcolor)

        # Save group plotting data to list
        saveGroups.append([plotGroupIdx,fossilGroup,datumType,avg_age, avg_depth,marker,markersize,color,fillstyle,label])

    # Add avg_age, avg_depth to dfDATUMS
    dfDATUMS['plot_age'] = xdata
    dfDATUMS['plot_depth'] = ydata

    # Turn lists into dataframe
    headers = ['plotGroupIdx','fossilGroup','datumType','avg_age','avg_depth',
               'marker','markersize','color','fillstyle','label']
    dfGROUPS = pd.DataFrame(saveGroups, columns=headers)

    # If any of the datums had a range, save to a group for line toggling
    dfRangeGROUPS = pd.DataFrame(saveRangeGroups, columns=['plotGroupIdx','rangeGroup', 'xline', 'yline', 'color']) if len(saveRangeGroups) > 0 else []
    # If any of the datums had a box range, save to a group for rectangle toggling
    dfRangeBOXES = pd.DataFrame(saveRangeBoxes, columns=['plotGroupIdx','boxGroup', 'xmin', 'ymax', 'xWidth','yHeight', 'color']) if len(saveRangeBoxes) > 0 else []
    # Extract line groups from dataframe, sort for legend
    lines = []
    lineGroups = pd.unique(dfGROUPS['plotGroupIdx'].tolist())
    lineGroups.sort()
    linesr = []  # Lines for ranges
    boxesr = []  # Boxes for ranges

    # Re-organize, plot, and save lines to list
    for i in range(0,len(lineGroups)):
       pltLine = dfGROUPS[(dfGROUPS.plotGroupIdx == lineGroups[i])]
       newIndex=range(0,len(pltLine))
       pltLine['newIndex'] = newIndex
       pltLine = pltLine.set_index('newIndex')
       xd = zip(pltLine['avg_age'])
       yd = zip(pltLine['avg_depth'])
       lid = 'line'+str(i)
       gid = str(lineGroups[i])
       lid, = plt.plot(xd, yd, marker=pltLine['marker'][0], markersize=pltLine['markersize'][0],
                       color=pltLine['color'][0], fillstyle=pltLine['fillstyle'][0], lw=0,
                       label=pltLine['fossilGroup'][0]+":"+ pltLine['datumType'][0],gid=gid)
       lines.append(lid)

    # Plot and save age-depth ranges to lines list
    for i in range(0,len(dfRangeGROUPS)):
       xd = dfRangeGROUPS['xline'][i]
       yd = dfRangeGROUPS['yline'][i]
       color = dfRangeGROUPS['color'][i]
       lidr = dfRangeGROUPS['rangeGroup'][i]+'.'+str(i)
       gid = str(dfRangeGROUPS['plotGroupIdx'][i])
       lidr, = plt.plot(xd, yd, color, linewidth=0.5, gid=gid)
       linesr.append(lidr)

    # Plot and save age-depth ranges box to boxes list
    for i in range(0,len(dfRangeBOXES)):
       xmin = dfRangeBOXES['xmin'][i]
       ymax = dfRangeBOXES['ymax'][i]
       xWidth = dfRangeBOXES['xWidth'][i]
       yHeight = dfRangeBOXES['yHeight'][i]
       color = dfRangeBOXES['color'][i]
       bidr = dfRangeBOXES['boxGroup'][i]+'.'+str(i)
       gid = str(dfRangeBOXES['plotGroupIdx'][i])
       rectangle = plt.Rectangle((xmin,ymax), xWidth, yHeight, facecolor=color, gid=gid)
       plt.gca().add_patch(rectangle)
       boxesr.append(rectangle)

    # Plot legend
    leg = plt.legend(bbox_to_anchor=(1.0025,0.75), loc=2, borderaxespad=0., numpoints=1)
    leg.get_frame().set_alpha(0.4)

    lined = dict()
    for legline, origline in zip(leg.get_lines(), lines):
        legline.set_picker(5)  # 5 pts tolerance
        lined[legline] = origline

    def on_legend_pick(event, lined):
        """Match picked legend line to original line and toggle visibility."""

        legline = event.artist
        origline = lined[legline]
        # Get texts of legend
        ltexts = leg.get_texts()
        # Get label of picked legend line
        legLabel = origline.get_label()
        # Toggle visibility of the picked line (fossil_group/datum_type)
        vis = not origline.get_visible()
        origline.set_visible(vis)
        # Get the gid of the line being toggled
        # Match to range lines, and toggle them too
        gid = origline.get_gid()
        for i in range(0,len(linesr)):
            theLine = linesr[i]
            if theLine.get_gid() == gid:
                theLine.set_visible(vis)
        # Match to range boxes, and toggle them too
        for i in range(0,len(boxesr)):
            theBox = boxesr[i]
            if theBox.get_gid() == gid:
                theBox.set_visible(vis)
        if vis:
            #legline.set_alpha(1.0)  # Doesn't help, markers not lines...
            # Set color of legend text to black (on)
            for i in range(0,len(ltexts)):
                if legLabel == ltexts[i].get_text():
                    ltexts[i].set_color('black')
                    break
        else:
            #legline.set_alpha(0.1)  # Doesn't help, markers not lines...
            # Set color of legend text to red (off)
            for i in range(0,len(ltexts)):
                if legLabel == ltexts[i].get_text():
                    ltexts[i].set_color('red')
                    break
        fig.canvas.draw()

    # Register the callback for picking a line legend
    #canvas = ax.figure.canvas
    canvas.mpl_connect('pick_event', lambda e:on_legend_pick(e, lined))
    # Use AnnoteFinder to identify datums on plot
    af = AnnoteFinder(xdata, ydata, plotCodeID)
    # Register the callback for AnnoteFinder
    canvas.mpl_connect('button_press_event',af)

def plot_cores(dfCORES,xMin,xMax,yMin,yMax):
    """Plot the cores and core sections."""
    # Calculate width of rectangle for plotting cores
    cWidth = (xMax - xMin) * .025
    # Build x values for rectangles
    xline=[]
    xline.append(xMax - cWidth / 5.)
    xline.append(xMax)

    for i in range(0,len(dfCORES)):
        if dfCORES['top_depth'][i] >= yMin and dfCORES['bottom_depth'][i] <= yMax:
            cHeight = abs((dfCORES['bottom_depth'][i] - dfCORES['top_depth'][i]))
            rectangle = plt.Rectangle((xMax - cWidth, dfCORES['top_depth'][i]),
                                       cWidth, cHeight, fc='none')
            plt.gca().add_patch(rectangle)
            plt.annotate(dfCORES['core'][i],xy=(xMax -cWidth / 2.,
                         dfCORES['top_depth'][i] + (cHeight / 2.)), size=6.,
                         ha='center', va='center')
            # Plot the section subdivisions
            sections = int(abs((dfCORES['top_depth'][i] -
                                dfCORES['bottom_depth'][i]) / 1.5))
            for j in range(1,sections+1):
                yline=[]
                yline.append(dfCORES['top_depth'][i] + j * 1.5)
                yline.append(dfCORES['top_depth'][i] + j * 1.5)
                plt.plot(xline, yline, 'r-', linewidth=1.0)

def plot_time_scale(dfTIME,xMin,xMax,yMin,yMax):
    """Plot the time scale boundaries."""
    scaleName = dfTIME['time_scale_name']
    ageLevel = dfTIME['age_level_name']
    ageName  = dfTIME['age_name']
    ageMinMa   = dfTIME['age_min_ma']
    ageMaxMa = dfTIME['age_max_ma']
    for i in range(0,len(ageName)):
        # Extract and clean up ageName (Upper/Middle/Early)
        if ageLevel[i] == 'Subepoch':
            ageName[i] = ageName[i][ageName[i].find(' ') + 1:]
            if ageName[i] == 'Upper':
                ageName[i] = 'Late'
            elif ageName[i] == 'Lower':
                ageName[i] = 'Early'

    # Pad on y-axis
    cHeight = -abs((yMax - yMin)*.025)
    yMinPad = yMin - (abs(yMax - yMin)*.05)

    # DEV: make a function to determine position relative to axes, and use
    # DEV: for stages and chrons, and...
    for i in range(0,len(dfTIME)):
        if (ageMinMa[i] >= xMin and ageMinMa[i] <= xMax and ageMaxMa[i] >= xMin and ageMaxMa[i] <= xMax) or (ageMinMa[i] < xMin and ageMaxMa[i] > xMin) or (ageMinMa[i] < xMax and ageMaxMa[i] > xMax):
            if ageLevel[i] == 'Epoch':
                rectangle = plt.Rectangle((ageMinMa[i],yMinPad-cHeight),ageMaxMa[i]-ageMinMa[i],cHeight,fc='none')
                plt.gca().add_patch(rectangle)
                rectangle = plt.Rectangle((ageMinMa[i],yMinPad-(cHeight*2.)),ageMaxMa[i]-ageMinMa[i],cHeight,fc='none')
                plt.gca().add_patch(rectangle)
                if ageMinMa[i] < xMin and ageName[i] != 'Holocene':
                    plt.annotate(ageName[i],xy=((xMin+ageMaxMa[i])/2.,yMinPad-(cHeight/2.)),size=9.,ha='center',va='center')
                elif ageMaxMa[i] > xMax and ageName[i] != 'Holocene':
                    plt.annotate(ageName[i],xy=((xMax+ageMinMa[i])/2.,yMinPad-(cHeight/2.)),size=9.,ha='center',va='center')
                elif ageName[i] != 'Holocene':
                    plt.annotate(ageName[i],xy=((ageMinMa[i]+ageMaxMa[i])/2.,yMinPad-(cHeight/2.)),size=9.,ha='center',va='center')
            elif ageLevel[i] == 'Subepoch':
            #elif (ageLevel[i] == 'Stage'): # DEV:  testing Stages, maybe an option?
                rectangle = plt.Rectangle((ageMinMa[i],yMinPad-(cHeight*2.)),ageMaxMa[i]-ageMinMa[i],cHeight,fc='none')
                plt.gca().add_patch(rectangle)
                if ageMinMa[i] < xMin:
                    plt.annotate(ageName[i],xy=((xMin+ageMaxMa[i])/2.,yMinPad-(cHeight*1.2)),size=8.,ha='center',va='top')
                elif ageMaxMa[i] > xMax:
                    plt.annotate(ageName[i],xy=((xMax+ageMinMa[i])/2.,yMinPad-(cHeight*1.2)),size=8.,ha='center',va='top')
                else:
                    plt.annotate(ageName[i],xy=((ageMinMa[i]+ageMaxMa[i])/2.,yMinPad-(cHeight*1.2)),size=8.,ha='center',va='top')

def plot_paleomag_interval(dfPMAGS,xMin,xMax,yMin,yMax):
    """Plot the pmag intervals."""
    xWidth = abs(xMax - xMin) * .0275
    topDepth = dfPMAGS['top_depth']
    bottomDepth = dfPMAGS['bottom_depth']
    intColor = dfPMAGS['color']
    for i in range(0,len(topDepth)):
        yHeight = abs(topDepth[i] - bottomDepth[i])
        if intColor[i] == 1:
            color='black'
        else:
            color='white'
        rectangle = plt.Rectangle((xMin, topDepth[i]), xWidth, yHeight,
                                   facecolor=color)
        plt.gca().add_patch(rectangle)

def plot_chrons(dfCHRONS,xMin,xMax,yMin,yMax):
    """Plot the paleomagnetic chrons."""
    # Plot the chrons
    # DEV: plot_chrons(dfCHRONS,xMin,xMax,yMin,yMax):  clean this up,
    # DEV: as in stages ... to make it easier to read and understand ...
    # DEV: note:  later might have all scales read, need to extract
    # DEV: current one being plotted ...

    # Calculate height of rectangle from Y axis range
    cHeight = -abs((yMax-yMin)*.025)
    for i in range(0,len(dfCHRONS)):
        if ((dfCHRONS['chron_age_min_ma'][i] >= xMin and dfCHRONS['chron_age_min_ma'][i] <= xMax
          and dfCHRONS['chron_age_max_ma'][i] >= xMin and dfCHRONS['chron_age_max_ma'][i] <= xMax)
          or (dfCHRONS['chron_age_min_ma'][i] <= xMin and dfCHRONS['chron_age_max_ma'][i] > xMin)
          or (dfCHRONS['chron_age_min_ma'][i] < xMax and dfCHRONS['chron_age_max_ma'][i] > xMax)):
            if dfCHRONS['chron_polarity_dir'][i] == None or pd.isnull(dfCHRONS['chron_polarity_dir'][i]): # None/NaN/NULL
                rectangle = plt.Rectangle((dfCHRONS['chron_age_min_ma'][i],yMax-cHeight),dfCHRONS['chron_age_max_ma'][i]-dfCHRONS['chron_age_min_ma'][i],cHeight,fc='none')
                plt.gca().add_patch(rectangle)
                rectangle = plt.Rectangle((dfCHRONS['chron_age_min_ma'][i],yMax-(cHeight*2.)),dfCHRONS['chron_age_max_ma'][i]-dfCHRONS['chron_age_min_ma'][i],cHeight,fc='none')
                plt.gca().add_patch(rectangle)
                if dfCHRONS['chron_age_min_ma'][i] < xMin:
                    plt.annotate(dfCHRONS['chron_name'][i][1:],xy=((xMin+dfCHRONS['chron_age_max_ma'][i])/2.,yMax-(cHeight/2.)),size=6.,ha='center',va='center')
                elif dfCHRONS['chron_age_max_ma'][i] > xMax:
                    plt.annotate(dfCHRONS['chron_name'][i][1:],xy=((xMax+dfCHRONS['chron_age_min_ma'][i])/2.,yMax-(cHeight/2.)),size=6.,ha='center',va='center')
                else:
                    plt.annotate(dfCHRONS['chron_name'][i][1:],xy=((dfCHRONS['chron_age_min_ma'][i]+dfCHRONS['chron_age_max_ma'][i])/2.,yMax-(cHeight/2.)),size=6.,ha='center',va='center')
            elif dfCHRONS['chron_polarity_dir'][i] == 'N': # Normal polarity
                rectangle = plt.Rectangle((dfCHRONS['chron_age_min_ma'][i],yMax-(cHeight*2.)),dfCHRONS['chron_age_max_ma'][i]-dfCHRONS['chron_age_min_ma'][i],cHeight,fc='black')
                plt.gca().add_patch(rectangle)

def plot_metadata(parent, xMin, xMax, yMin, yMax, data):
    """Plot metadata."""
    userName = data['user']
    stratFileName = data['stratFileName']
    locFileName = data['LOCFileName'][parent.locIdx] if type(data['LOCFileName']) is list else data['LOCFileName']
    # Plot userName, stratFileName, locFileName, and timestamp
    # Get the current timestamp
    stamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    # Strip path from stratFileName and plot
    if '/' in stratFileName:
        stratFileName = stratFileName[stratFileName.rfind('/')+1:]
    plt.text(xMax,yMax - (abs(yMin)-abs(yMax))*.125,'Strat: ' + stratFileName,size=8., ha='right')
    # Strip path from locFileName and plot
    if '/' in locFileName:
        locFileName = locFileName[locFileName.rfind('/')+1:]
    # If locFileName plot
    if len(data['phantom']):
        plt.text(xMax,yMax - (abs(yMin)-abs(yMax))*.150,'Active LOC: ' + locFileName + ' | Phantom LOC: ' + data['phantom']['loc_name'],size=8., ha='right')
    else:
        plt.text(xMax,yMax - (abs(yMin)-abs(yMax))*.150,'LOC: ' + locFileName,size=8., ha='right')
    plt.text(xMax,yMin + (abs(yMin)-abs(yMax))*.10,userName,size=8., ha='right')
    plt.text(xMax,yMin + (abs(yMin)-abs(yMax))*.075,stamp,size=8., ha='right')

def set_labels(labels):
    """Set axes values for plot."""
    new_labels = LabelDialog(labels)
    if new_labels.ShowModal()== wx.ID_OK:
        title = str(new_labels.title.GetValue())
        xaxis = str(new_labels.xaxis.GetValue())
        yaxis = str(new_labels.yaxis.GetValue())
        return [title,xaxis,yaxis]
    else:
        return labels

def set_axes(parent, axes):
    """Set axes values for plot."""
    while 1:
        new_axes = AxisDialog([axes[0], axes[1], axes[3], axes[2]])
        if new_axes.ShowModal()== wx.ID_OK:
            xmin = float(new_axes.xmin.GetValue())
            xmax = float(new_axes.xmax.GetValue())
            ymax = float(new_axes.ymin.GetValue())
            ymin = float(new_axes.ymax.GetValue())
            fieldValues = [xmin, xmax, ymin, ymax]
            if fieldValues is None:
                fieldValues = axes
                break
            errmsg = ""
            if fieldValues[0] >= fieldValues[1]: errmsg = 'youngest age should be < to oldest age.\n'
            if fieldValues[2] >= fieldValues[3]: errmsg = 'higher depth should be < to lower depth.\n'
            if errmsg == "": break
            else: parent.messageboard.WriteText("Error: " + errmsg)
        else:
            fieldValues = axes
            break
    return fieldValues

class AnnoteFinder: #Pat's code, largely untouched
    """
    Callback for matplotlib to display an annotation when points are clicked on.
    The point which is closest to the click and within xtol and ytol is
     identified.

    Register this function like this:

    scatter(xdata, ydata)
    af = AnnoteFinder(xdata, ydata, annotes)
    connect('button_press_event', af)
    """
    # DEV: class AnnoteFinder:   code copied, modified from jkitchin
    # DEV: see jkitchin on GitHub
    # DEV: John Kitchin, Carnegie Mellon University (jkitchin@andrew.cmu.edu)
    # DEV: code from annotate_picks.py and mmapsrep.py

    def __init__(self,xdata,ydata,annotes,axis=None,xtol=None,ytol=None):
        self.ANN = zip(xdata,ydata,annotes)
        if xtol is None:
            xtol = 0.1
        if ytol is None:
            ytol = 1.5
        self.xtol = xtol
        self.ytol = ytol
        self.axis = axis if axis is not None else plt.gca()
        self.drawnAnnotations = {}
        self.links = []

    def __call__(self,event):
        if event.inaxes:
          clickX = event.xdata
          clickY = event.ydata
          if self.axis is None or self.axis==event.inaxes:
            annotes = []
            for x,y,a in self.ANN:
                if clickX-self.xtol < x < clickX+self.xtol and clickY-self.ytol < y < clickY+self.ytol:
                    # DEV:  added button check
                    if event.button == 1 or event.button == 2:
                        a = a[0]+":"+a[2]  # For plot_code, plot_color
                        btn = event.button
                    else:
                        a = a[0]+":"+a[1]+":"+a[2] # For plot_code, datum_name, color
                        btn = 3
                    annotes.append((math.hypot(x - clickX, y - clickY),x,y,a))

            if annotes:
                # DEV: modification:  report all at x,y
                for i in range(0,len(annotes)):
                    distance, x, y, annote = annotes[i]
                    #self.drawAnnote(event.inaxes,x,y,annote) # Modification
                    self.drawAnnote(event.inaxes,x,y,annote,clickX,clickY,i,btn)
                    for j in self.links:
                        j.drawSpecificAnnote(annote)

    # Modification: added clickX,clickY,idx
    def drawAnnote(self,axis,x,y,annote,clickX,clickY,idx,btn):
        """
        Draw the annotation on the plot
        """
        if self.drawnAnnotations.has_key((x,y)): # Modification
            markers = self.drawnAnnotations[(x,y)]
            for m in markers:
                m.set_visible(not m.get_visible())
            self.axis.figure.canvas.draw()
            del self.drawnAnnotations[(x,y)] # Modification
        else:
            color  = annote[annote.rfind(':',0)+1:]
            annote = annote[0:annote.rfind(':',0)]
            if clickX <= x: # DEV: figure quadrant to post text
                xpos = x - .10
                ha = 'right'
            else:
                xpos = x + .10
                ha = 'left'
            if clickY <= y:
                ypos = y - .10
                va = 'top' if idx == 0 else 'bottom'
            else:
                ypos = y + .10
                va = 'bottom' if idx == 0 else 'top'
            if btn == 1:
                t = axis.text(xpos,ypos,"%s"%(annote),size=7.,color=color,horizontalalignment=ha,verticalalignment=va)
            else:
                t = axis.text(xpos,ypos,"%s (%6.3f, %8.3f)"%(annote,x,y),size=7.,color=color,horizontalalignment=ha,verticalalignment=va)
            #m = axis.scatter([x],[y],marker='o',s=128,alpha=0.4,c='yellow') # DEV: highlight with yellow circle
            m = axis.scatter([x],[y],marker='.',s=0,c='k',zorder=100) # DEV: modified, s=0 to show text only
            self.drawnAnnotations[(x,y)]=(t,m)
            self.axis.figure.canvas.draw()

        # DEV: can use this code with modification to toggle on/off all annotations
        # DEV: modify code for event with key_pressed 't' or 'a' ....
        # DEV: see annotation_picks_ALL.py that shows modifications (don't check for distance/xtol/ytol)

    def drawSpecificAnnote(self,annote):
        annotesToDraw = [(x,y,a) for x,y,a in self.data if a==annote]
        for x,y,a in annotesToDraw:
            self.drawAnnote(self.axis,x,y,a)

# Pat functions adapted to wx by JR:
# READ_ functions:

def read_gpts(parent):
    """Read GPTS from file."""
    parent.messageboard.WriteText('reading GPTS for converting ages\n')
    fileName = os.environ['NSBPATH'] + "/REF/gpts.txt"
    dfGPTS = pd.read_csv(fileName, delimiter='\t', header=0, skiprows=1,
                         names=['event_id', 'event_type', 'event_name',
                                'age_ma', 'scale'],
                         usecols=[0,1,2,3,4])
    return dfGPTS

def read_paleomag_scale(parent,toScale):
    """Read CHRON intervals from file."""
    parent.messageboard.WriteText('reading paleomag scale data file\n')
    fileName = os.environ['NSBPATH'] + "/REF/paleomagscale.txt"
    dfCHRONS = pd.read_csv(fileName, delimiter='\t', header=0, skiprows=1,
                           names=['paleomag_scale_name',
                                  'chron_name', 'chron_alias',
                                  'chron_polarity_dir', 'chron_age_min_ma',
                                  'chron_age_max_ma', 'chron_id',
                                  'parent_chron_id'],
                           usecols=[0,1,2,3,4,5,6,7])
    df = dfCHRONS[dfCHRONS.paleomag_scale_name == toScale]
    newIndex=range(0,len(df))
    df['newIndex'] = newIndex
    df = df.set_index('newIndex')
    return df

def read_time_scale(parent, toScale):
    """Read geological timescale data from a file."""
    parent.messageboard.WriteText('reading timescale data file\n')
    fileName = os.environ['NSBPATH'] + "/REF/timescale.txt"
    dfTIME = pd.read_csv(fileName, delimiter='\t', header=0, skiprows=1,
                           names=['time_scale_name', 'age_level_name',
                                  'age_name', 'age_min_ma', 'age_max_ma',
                                  'age_id', 'parent_age_id'],
                           usecols=[0,1,2,3,4,5,6])
    df = dfTIME[dfTIME.time_scale_name == toScale]
    newIndex=range(0,len(df))
    df['newIndex'] = newIndex
    df = df.set_index('newIndex')
    return df

def read_datums(parent,fileName, data):
    """Read datum strat events from file."""
    df = [] # Return empty if Cancel on read
    parent.messageboard.WriteText('reading strat (datums) data file\n')
    datumType = []
    if fileName == '.':
        parent.messageboard.WriteText('no strat datums read\n')
        return df
    r = csv.reader(open(fileName,'rU'),delimiter='\t')
    d = []
    n = 0
    for row in r:
        n += 1
        if n == 1: # Header
            check_holeID = row[0].upper()
            if check_holeID != data['holeID']:
                parent.messageboard.WriteText("*** Wrong holeID: " + check_holeID + " ***\n")
                parent.messageboard.WriteText("*** Skipping read strat file, will not plot ***\n")
                return df
            #timescale = row[1] # Not used but for clarification on time scale ...
            data['fromScale'] = row[2] # Global fromScale for paleomag age conversions
            if data['fromScale'] not in set(data['dfGPTS']['scale']):
                parent.messageboard.WriteText("*** Unknown GPTS scale: " + data['fromScale'] + " ***\n")
                return df
        if n > 2  and len(row)>1 and not(row[0].startswith("#")): # Data
            d.append({'plot_fossil_group':row[0], 'datum_name':row[1],
                      'plot_code':row[2], 'datum_age_min_ma':row[3],
                      'datum_age_max_ma':row[4], 'top_depth':row[5],
                      'bottom_depth':row[6]})
    df = pd.DataFrame(d, columns = ['plot_fossil_group', 'datum_name',
                                'plot_code', 'datum_age_min_ma',
                                'datum_age_max_ma', 'top_depth',
                                'bottom_depth'])
    for i in range(len(df)):
        df['plot_fossil_group'][i] = df['plot_fossil_group'][i].strip()
        df['plot_code'][i] = df['plot_code'][i].strip()
        df['datum_name'][i] = df['datum_name'][i].strip()
        df['top_depth'][i] = df['top_depth'][i].strip()
        df['bottom_depth'][i] = fix_null(df['bottom_depth'][i],0)
        if df['bottom_depth'][i] is None:
            df['bottom_depth'][i] = df['top_depth'][i]
        df['top_depth'][i] = fix_null(df['top_depth'][i],0)
        df['bottom_depth'][i] = fix_null(df['bottom_depth'][i],0)
        df['datum_age_min_ma'][i] = fix_null(df['datum_age_min_ma'][i],1)
        df['datum_age_max_ma'][i] = fix_null(df['datum_age_max_ma'][i],1)
        if df['datum_age_min_ma'][i] is None:
            df['datum_age_min_ma'][i] = df['datum_age_max_ma'][i]
        elif df['datum_age_max_ma'][i] is None:
            df['datum_age_max_ma'][i] = df['datum_age_min_ma'][i]
        if df['top_depth'][i].find('-') > 0:
            if df['top_depth'][i] == '0-0,0':
                df['top_depth'][i] = 0.
            else:
                df['top_depth'][i] = calc_core_depth(df['top_depth'][i],data['dfCORES'])
        else:
            df['top_depth'][i] = float(df['top_depth'][i])
        if df['bottom_depth'][i].find('-') > 0:
            df['bottom_depth'][i] = calc_core_depth(df['bottom_depth'][i],data['dfCORES'])
        else:
            df['bottom_depth'][i] = float(df['bottom_depth'][i])
        typDat = df['plot_code'][i][0].upper() if len(df['plot_code'][i]) else ''
        datumType.append(typDat)
    df['datum_type'] = datumType
    return df

def read_cores(parent,fileName,data):
    """Read cores file."""
    df = [ ] # Return empty if cancel on read
    parent.messageboard.WriteText('reading core data file\n')
    if fileName == '.':
        parent.messageboard.WriteText('no cores read\n')
        return df
    r = csv.reader(open(fileName,'rU'),delimiter='\t')
    d = []
    n = 0
    for row in r:
        n += 1
        if n == 1: # Extract global holeID
            data['holeID'] = row[0].upper()
        if n > 2  and len(row)>1 and not(row[0].startswith("#")): # Data lines
            d.append({'core':int(row[0]), 'top_depth':float(row[1]),
                      'bottom_depth':float(row[2])})
    df = pd.DataFrame(d, columns = ['core', 'top_depth', 'bottom_depth'])
    return df

def read_paleomag_interval(parent,fileName):
    """Read PMAG intervals from file."""
    df = [ ] # Return empty if cancel on read
    parent.messageboard.WriteText('reading paleomag interval data file\n')
    if fileName != '.':
        r = csv.reader(open(fileName,'rU'),delimiter='\t')
        d = []
        n = 0
        for row in r:
            n += 1
            if n == 1: # Check that the holeID is the correct one
                check_holeID = row[0].upper()
                if check_holeID != holeID:
                    parent.messageboard.WriteText("*** Wrong PMAG holeID: " + check_holeID + " ***\n")
                    parent.messageboard.WriteText("*** Skipping read PMAG file, will not plot ***\n")
                    return df
            if n > 2  and len(row)>1 and not(row[0].startswith("#")): # Data lines
                d.append({'top_depth':float(row[0]),
                          'bottom_depth':float(row[1]), 'color':int(row[2]),
                          'pattern':row[3], 'width':float(row[4])})
        df = pd.DataFrame(d, columns = ['top_depth', 'bottom_depth',
                                        'color', 'pattern', 'width'])
    return df

def read_loc(parent,fileName, data):
    """ Read LOC from file.""" # To extract from file for age conversions (paleomag scale)
    df = [] # Return empty if Cancel on read
    parent.messageboard.WriteText('reading LOC data file\n')
    if fileName != '.': # Check for Cancel
        r = csv.reader(open(fileName,'rU'),delimiter='\t')
        d = []
        n = 0
        for row in r:
            n += 1
            if n == 1: # Check that the holeID is the correct one
                check_holeID = row[0].upper()
                if check_holeID != data['holeID']:
                    parent.messageboard.WriteText("*** Wrong LOC holeID: " + check_holeID + " ***\n")
                    parent.messageboard.WriteText("*** Beware that this LOC was not prepared for this hole! ***\n")
                    parent.messageboard.WriteText("*** If this was not intentional, you can add the correct LOC using the menu option. ***\n")
                    #parent.messageboard.WriteText("*** Skipping read LOC file, will not plot ***\n")
                    #return df
                #timeScale = row[1] # Time scale, e.g., Berg95
                fromScale = row[1] # Paleomag chron scale, e.g., CK95
                if fromScale not in set(data['dfGPTS']['scale']):
                    parent.messageboard.WriteText("*** Unknown GPTS scale: " + fromScale + " ***\n")
                    return df
            if n > 2  and len(row)>1 and not(row[0].startswith("#")): # Data lines
                try:
                    d.append({'age_ma':float(row[0]), 'depth_mbsf':float(row[1])})
                except:
                    parent.messageboard.WriteText("*** Non-numerical value in row " + str(n) + ", LOC not plotting ***\n")
                    return []
        df = pd.DataFrame(d, columns = ['age_ma', 'depth_mbsf'])
        for i in range(len(df)):
            df['depth_mbsf'][i] = fix_null(df['depth_mbsf'][i],1)
        if fromScale != data['toScale']:
            fromAgeDict = data['dfGPTS'][['event_id','age_ma']][data['dfGPTS'].scale == fromScale].to_dict('records')
            toAgeDict = data['dfGPTS'][['event_id','age_ma']][data['dfGPTS'].scale == data['toScale']].to_dict('records')
            for i in range(0,len(df)):
                locAge = df['age_ma'][i]
                df['age_ma'][i] = float(str(round(age_convert(locAge, fromAgeDict, toAgeDict),3)))
    return df

#SAVE_ functions:
def save_loc(parent, holeID, x, y): #Rewritten
    """Write the current LOC to a file."""
    file = holeID + "_loc.txt"
    default = os.environ['NSBPATH'] + "/LOC/"
    wildcard = "Tab-separated files (*.txt)|*.txt"
    dlg = wx.FileDialog(None, 'Save your file', defaultDir =default, defaultFile=file, wildcard=wildcard, style=wx.FD_SAVE)
    if dlg.ShowModal() == wx.ID_OK:
        fileName = dlg.GetPath()
        toScale = data['toScale'] # For timescale and paleomag chron scale
        date = datetime.date.today().isoformat()
        fo = open(fileName,"w")
        fo.write(holeID+"\t"+toScale+"\t"+toScale+"\t"+date+"\n")
        fo.write("AGE"+"\t"+"DEPTH"+"\n")
        for i in range (len(x)):
            fo.write(str(round(x[i],6))+"\t"+str(abs(round(y[i],3)))+"\n")
        fo.close()
        parent.messageboard.WriteText('saving LOC to %s\n' % (fileName,))

def save_plot(parent, holeID, fig): #Rewritten
    """Save plot figure to a file."""
    stamp = datetime.datetime.now().strftime("%Y-%m-%d-%H-%M-%S")
    path = os.environ['NSBPATH'] + "/PLOTS/"
    file = holeID + "_" + stamp + ".png"
    wildcard = "PNG files (*.png)|*.png|PDF files (*.pdf)|*.pdf|SVG files (*.svg)|*.svg|TIFF files (*.tiff)|*.tiff"
    dlg = wx.FileDialog(None, 'Save your file', defaultDir=path, defaultFile=file, wildcard=wildcard, style=wx.FD_SAVE)
    if dlg.ShowModal() == wx.ID_OK:
        fileName = dlg.GetPath()
        fig.savefig(fileName)
    parent.messageboard.WriteText('saving figure to %s\n' % (fileName,))

def project_events(parent, data,x,y):
    """Write projected ages of events to file"""
    file = data['holeID'] + "_proj.txt"
    default = os.environ['NSBPATH'] + "/PROJ/"
    wildcard = "Tab-separated files (*.txt)|*.txt"
    dlg = wx.FileDialog(None, 'Save your file', defaultDir =default, defaultFile=file, wildcard=wildcard, style=wx.FD_SAVE)
    if dlg.ShowModal() == wx.ID_OK:
        fileName = dlg.GetPath()
        # Extract a subset of column data in a new order for reporting
        dfLIST = data['dfDATUMS'][['plot_fossil_group', 'datum_type', 'datum_name',
                           'plot_code', 'plot_depth', 'plot_age']]
        # Sort by fossil group, depth, name
        dfLIST = dfLIST.sort_values(['plot_fossil_group', 'plot_depth', 'datum_name'],
                              ascending=[True,False,True])
        # Re-index the new sorted dataframe
        newIndex=range(0,len(dfLIST))
        dfLIST['newIndex'] = newIndex
        dfLIST = dfLIST.set_index('newIndex')
        fo = open(fileName,"w")
        date = datetime.date.today().isoformat()
        header = []
        header.append(data['holeID'])
        header.append('v0.5')
        header.append(date)
        header.append('nsb_adp.py Program')
        header.append('Projected Ages')
        fo.write("\t".join(map(str,header))+"\n")
        colHdr = []
        colHdr.append('fossil_group')
        colHdr.append('datum_type')
        colHdr.append('datum_name')
        colHdr.append('plot_code')
        colHdr.append('plot_depth')
        colHdr.append('plot_age')
        colHdr.append('proj_age')
        colHdr.append('proj_age_extension')
        fo.write("\t".join(map(str,colHdr))+"\n")

        for i in range(0,len(dfLIST)):
            # DEV: Check for hiatus?
            proj_age = calc_depth_ma(abs(dfLIST['plot_depth'][i]), x, y)
            if dfLIST['plot_age'][i] is not np.nan and proj_age is not None:
                proj_age_extension = proj_age - dfLIST['plot_age'][i]
            else:
                proj_age_extension = None
            row = []
            row.append(dfLIST['plot_fossil_group'][i])
            row.append(dfLIST['datum_type'][i])
            row.append(dfLIST['datum_name'][i])
            row.append(dfLIST['plot_code'][i])
            row.append(str(dfLIST['plot_depth'][i]))
            row.append(str(dfLIST['plot_age'][i]))
            row.append(str(round(proj_age,3)) if proj_age is not None else '')
            row.append(str(round(proj_age_extension,3)) if proj_age_extension is not None else '')
            fo.write("\t".join(map(str,row))+"\n")

        fo.close()

def convert_agescale_DB(data):
    toScale = data['toScale']
    toAgeDict = data['dfGPTS'][['event_id','age_ma']][(data['dfGPTS'].scale == toScale)].to_dict('records')
    origMaxAge = []
    origMinAge = []
    # Check each datum and convert age if source scale different than target (Grad12)
    for i in range(0,len(data['dfDATUMS'])):
        fromScale = data['dfDATUMS']['scale'][i]
        fromAgeDict = data['dfGPTS'][['event_id','age_ma']][data['dfGPTS'].scale == fromScale].to_dict('records')
        maxAge = data['dfDATUMS']['datum_age_max_ma'][i]
        minAge = data['dfDATUMS']['datum_age_min_ma'][i]
        origMaxAge.append(maxAge) # Save original
        origMinAge.append(minAge) # Save original
        if fromScale is not None: #If fromScale is None it means that there is no calibration in the DB for that event so no need to convert
            if fromScale != toScale: # If the fromScale != toScale, convert age for every point ...
                data['dfDATUMS']['datum_age_max_ma'][i] = float(str(round(age_convert(maxAge, fromAgeDict, toAgeDict),3)))
                if maxAge != minAge:
                    data['dfDATUMS']['datum_age_min_ma'][i] = float(str(round(age_convert(minAge, fromAgeDict, toAgeDict),3)))
                else:
                    data['dfDATUMS']['datum_age_min_ma'][i] = data['dfDATUMS']['datum_age_max_ma'][i]
    data['dfDATUMS']['origMaxAge'] = origMaxAge
    data['dfDATUMS']['origMinAge'] = origMinAge
    return data['dfDATUMS']

def convert_agescale_file(toScale, fromScale, dfGPTS, dfDATUMS):
    toAgeDict = dfGPTS[['event_id','age_ma']][(dfGPTS.scale == toScale)].to_dict('records')
    origMaxAge = []
    origMinAge = []
    # Check each datum and convert age if source scale different than target (Grad12)
    for i in range(0,len(dfDATUMS)):
        fromAgeDict = dfGPTS[['event_id','age_ma']][dfGPTS.scale == fromScale].to_dict('records')
        maxAge = dfDATUMS['datum_age_max_ma'][i]
        minAge = dfDATUMS['datum_age_min_ma'][i]
        origMaxAge.append(maxAge) # Save original
        origMinAge.append(minAge) # Save original
        if fromScale != toScale: # If the fromScale != toScale, convert age for every point ...
            dfDATUMS['datum_age_max_ma'][i] = float(str(round(age_convert(maxAge, fromAgeDict, toAgeDict),3)))
            if maxAge != minAge:
                dfDATUMS['datum_age_min_ma'][i] = float(str(round(age_convert(minAge, fromAgeDict, toAgeDict),3)))
            else:
                dfDATUMS['datum_age_min_ma'][i] = dfDATUMS['datum_age_max_ma'][i]
    dfDATUMS['origMaxAge'] = origMaxAge
    dfDATUMS['origMinAge'] = origMinAge
    return dfDATUMS

# New GUI (JR) below:
# Wrappers:

def ADP_Menubar(parent): # Menubar
    menubar = wx.MenuBar()
    File = wx.Menu()
    File1 = File.Append(wx.ID_EXIT, 'Quit')
    View = wx.Menu()
    View1 = View.Append(wx.ID_ANY, 'Help')
    menubar.Append(File, 'File')
    menubar.Append(View, 'View')
    parent.Bind(wx.EVT_MENU, parent.Quit, File1)
    parent.Bind(wx.EVT_MENU, lambda event: parent.GenericHelp(event), View1)
    return menubar

def Ok_Cancel_Wrapper(parent): # Self-Explanatory
    hor = wx.BoxSizer(wx.HORIZONTAL)
    okButton = wx.Button(parent, wx.ID_OK, "OK")
    okButton.SetDefault()
    hor.Add(okButton)
    hor.Add((20,20))
    cancelButton = wx.Button(parent, wx.ID_CANCEL, "Cancel")
    hor.Add(cancelButton)
    return hor

# Dialogs:
class HoleQueryDialog(wx.Dialog): # Dialog to choose hole from db
    def __init__(self, parent, engine):
        wx.Dialog.__init__(self, parent, -1, 'Select a Hole', size=(400,200), pos=(200,200))
        self.index = 0
        parent.messageboard.WriteText('retrieving holes from database\n')
        sqlHOLES = """
        WITH A as (SELECT hole_id, COUNT(DISTINCT(sample_id)) as n_samples,
              latitude, longitude, water_depth, ocean_code, meters_penetrated, meters_recovered,leg, site_hole
        	  FROM neptune_hole_summary FULL JOIN neptune_sample USING (hole_id)
        	  GROUP BY 1, 3, 4, 5, 6, 7, 8, 9, 10),
        	 B as (SELECT hole_id, COUNT(DISTINCT(es_id)) as n_events
              FROM neptune_hole_summary as nhs FULL JOIN neptune_event as ne ON nhs.hole_id=ne.top_hole_id
              GROUP BY 1),
        	 C as (SELECT hole_id, COUNT(DISTINCT(revision_no)) AS age_model
              FROM neptune_hole_summary FULL JOIN neptune_age_model_history USING (site_hole)
              GROUP BY 1),
        	 D as (SELECT *
              FROM A FULL JOIN B USING (hole_id)
        	  WHERE hole_id IS NOT NULL)
        SELECT *
        FROM D FULL JOIN C USING (hole_id)
        WHERE N_events>0 OR age_model>0
        ORDER BY leg, site_hole;
        """
        dfHOLES = psql.read_sql_query(sqlHOLES, engine)
        dfHoleList = dfHOLES[['hole_id','ocean_code','latitude','longitude','n_samples','n_events','age_model',
                        'water_depth','meters_penetrated','meters_recovered']]
        self.holeList = dfHoleList.to_dict('records')
        self.list_ctrl = wx.ListCtrl(self, size=(750,450), style = wx.LC_REPORT|wx.BORDER_SUNKEN|wx.LC_SINGLE_SEL)
        self.list_ctrl.InsertColumn(0,'hole_id', width=100)
        self.list_ctrl.InsertColumn(1,'ocean', width=50)
        self.list_ctrl.InsertColumn(2,'latitude',format=wx.LIST_FORMAT_RIGHT, width=60)
        self.list_ctrl.InsertColumn(3,'longitude',format=wx.LIST_FORMAT_RIGHT, width=60)
        self.list_ctrl.InsertColumn(4,'sample count',format=wx.LIST_FORMAT_RIGHT)
        self.list_ctrl.InsertColumn(5,'event count',format=wx.LIST_FORMAT_RIGHT)
        self.list_ctrl.InsertColumn(6,'age model?',format=wx.LIST_FORMAT_RIGHT)
        self.list_ctrl.InsertColumn(7,'water depth',format=wx.LIST_FORMAT_RIGHT)
        self.list_ctrl.InsertColumn(8,'penetrated',format=wx.LIST_FORMAT_RIGHT, width=70)
        self.list_ctrl.InsertColumn(9,'recovered',format=wx.LIST_FORMAT_RIGHT, width=70)
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(self.list_ctrl, 0, wx.ALL|wx.EXPAND, 5)
        for i in self.holeList:
            self.list_ctrl.InsertStringItem(self.index, str(i['hole_id']))
            self.list_ctrl.SetStringItem(self.index, 1, str(i['ocean_code']))
            self.list_ctrl.SetStringItem(self.index, 2, str(round(i['latitude'],2)))
            self.list_ctrl.SetStringItem(self.index, 3, str(round(i['longitude'],2)))
            self.list_ctrl.SetStringItem(self.index, 4, str(i['n_samples']))
            self.list_ctrl.SetStringItem(self.index, 5, str(i['n_events']))
            self.list_ctrl.SetStringItem(self.index, 6, str(bool(i['age_model'])))
            self.list_ctrl.SetStringItem(self.index, 7, str(i['water_depth']))
            self.list_ctrl.SetStringItem(self.index, 8, str(i['meters_penetrated']))
            self.list_ctrl.SetStringItem(self.index, 9, str(i['meters_recovered']))
            self.index += 1
        hor = Ok_Cancel_Wrapper(self)
        sizer.Add((20,20))
        sizer.Add(hor,0,wx.CENTER)
        sizer.Add((20,20))
        self.SetSizerAndFit(sizer)
        self.Layout()

class FileOrDbDialog(wx.Dialog):
    def __init__(self, parent):
        wx.Dialog.__init__(self, parent, -1, 'Select a source', size=(200,50), pos=(200,200))
        sizer = wx.BoxSizer(wx.VERTICAL)
        self.source = wx.RadioBox(self, choices=['NSB Database','Local File'], majorDimension=1, style=wx.RA_SPECIFY_ROWS)
        sizer.Add(self.source, 0, wx.ALL|wx.EXPAND, 5)
        hor = Ok_Cancel_Wrapper(self)
        sizer.Add((20,20))
        sizer.Add(hor,0,wx.CENTER)
        sizer.Add((20,20))
        self.SetSizerAndFit(sizer)
        self.Layout()

class RevisionDialog(wx.Dialog): # Dialog to choose hole from db
    def __init__(self, parent, revision_no):
        wx.Dialog.__init__(self, parent, -1, 'Select an age model', size=(600,50), pos=(200,200))
        self.index = 0
        sizer = wx.BoxSizer(wx.VERTICAL)
        self.list_ctrl = wx.ListCtrl(self, size=(750,150), style = wx.LC_REPORT|wx.BORDER_SUNKEN|wx.LC_SINGLE_SEL)
        self.amList = revision_no.to_dict('records')
        self.amList = sorted(self.amList,key=lambda x: [x['current_flag'],x['rn']],reverse=True)
        self.list_ctrl.InsertColumn(0,'revision_no',width=60)
        self.list_ctrl.InsertColumn(1,'current',width=50)
        self.list_ctrl.InsertColumn(2,'quality',width=50)
        self.list_ctrl.InsertColumn(3,'interpreted by',width=100)
        self.list_ctrl.InsertColumn(4,'date worked',width=100)
        self.list_ctrl.InsertColumn(5,'comments', width=700)
        sizer.Add(self.list_ctrl, 0, wx.ALL|wx.EXPAND, 5)
        for i in self.amList:
            self.list_ctrl.InsertStringItem(self.index, str(i['rn']))
            self.list_ctrl.SetStringItem(self.index, 1, str(i['current_flag']))
            self.list_ctrl.SetStringItem(self.index, 2, str(i['age_quality']))
            self.list_ctrl.SetStringItem(self.index, 3, str(i['interpreted_by']))
            self.list_ctrl.SetStringItem(self.index, 4, str(i['date_worked']))
            self.list_ctrl.SetStringItem(self.index, 5, str(i['remark']))
            self.index += 1
        self.list_ctrl.Select(0)
        hor = Ok_Cancel_Wrapper(self)
        sizer.Add((20,20))
        sizer.Add(hor,0,wx.CENTER)
        sizer.Add((20,20))
        self.SetSizerAndFit(sizer)
        self.Layout()

class GetFilesDialog(wx.Dialog): # Dialog to choose files to work with
    def __init__(self, parent, data):
        wx.Dialog.__init__(self, parent, -1, 'Load relevant files', size=(400,180))
        flex = wx.FlexGridSizer(9,3,5,5)
        flex.Add(wx.StaticText(self, label= ' User Name: ', style=wx.ALIGN_LEFT))
        self.user = wx.TextCtrl(self, size=(300,-1))
        flex.Add(self.user)
        if 'user' in data.keys(): self.user.SetValue(data['user'])
        flex.Add(wx.StaticText(self), wx.EXPAND)
        flex.Add(wx.StaticText(self, label= ' Core File ', style=wx.ALIGN_LEFT))
        self.corefile = wx.TextCtrl(self, size=(300,-1))
        button_core = wx.Button(self,wx.ID_ANY, label='Find core file')
        button_core.Bind(wx.EVT_BUTTON, self.CoreLookUp)
        flex.Add(self.corefile)
        flex.Add(button_core)
        flex.Add(wx.StaticText(self, label= ' Strat File ', style=wx.ALIGN_LEFT))
        self.stratfile = wx.TextCtrl(self, size=(300,-1))
        button_strat = wx.Button(self,wx.ID_ANY, label='Find strat file')
        button_strat.Bind(wx.EVT_BUTTON, self.StratLookUp)
        flex.Add(self.stratfile)
        flex.Add(button_strat)
        if data['plotPMAG'] == 1:
            flex.Add(wx.StaticText(self, label= ' Pmag File ', style=wx.ALIGN_LEFT))
            self.pmagfile = wx.TextCtrl(self, size=(300,-1))
            button_pmag = wx.Button(self,wx.ID_ANY, label='Find pmag file')
            button_pmag.Bind(wx.EVT_BUTTON, self.pmagLookUp)
            flex.Add(self.pmagfile)
            flex.Add(button_pmag)
        flex.Add(wx.StaticText(self, label= ' LOC File ', style=wx.ALIGN_LEFT))
        self.locfile = wx.TextCtrl(self, size=(300,-1))
        button_loc = wx.Button(self,wx.ID_ANY, label='Find LOC file')
        button_loc.Bind(wx.EVT_BUTTON, self.locLookUp)
        flex.Add(self.locfile)
        flex.Add(button_loc)
        flex.AddGrowableCol(1)
        hor = Ok_Cancel_Wrapper(self)
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(flex)
        sizer.Add((20,20))
        sizer.Add(hor,0,wx.CENTER)
        sizer.Add((20,20))
        self.SetSizerAndFit(sizer)
        self.Layout()

    def CoreLookUp(self,event):
        dirname = os.path.realpath(os.environ['NSBPATH'] + "/CORE/")
        dlg = wx.FileDialog(self, 'Choose your file', dirname)
        if dlg.ShowModal() == wx.ID_OK: self.corefile.SetValue(dlg.GetPath())
        dlg.Destroy()

    def StratLookUp(self,event):
        dirname = os.path.realpath(os.environ['NSBPATH'] + "/STRAT/")
        dlg = wx.FileDialog(self, 'Choose your file', dirname)
        if dlg.ShowModal() == wx.ID_OK: self.stratfile.SetValue(dlg.GetPath())
        dlg.Destroy()

    def pmagLookUp(self,event):
        dirname = os.path.realpath(os.environ['NSBPATH'] + "/PMAG/")
        dlg = wx.FileDialog(self, 'Choose your file', dirname)
        if dlg.ShowModal() == wx.ID_OK: self.pmagfile.SetValue(dlg.GetPath())
        dlg.Destroy()

    def locLookUp(self,event):
        dirname = os.path.realpath(os.environ['NSBPATH'] + "/LOC/")
        dlg = wx.FileDialog(self, 'Choose your file', dirname)
        if dlg.ShowModal() == wx.ID_OK: self.locfile.SetValue(dlg.GetPath())
        dlg.Destroy()

class dbDialog(wx.Dialog): # Dialog for db connexion
    def __init__(self, parent,data):
        wx.Dialog.__init__(self, parent, -1, 'Enter login information', size=(400,180))
        flex = wx.FlexGridSizer(9,2,5,5)
        flex.Add(wx.StaticText(self, label= ' Connexion ', style=wx.ALIGN_LEFT))
        self.source = wx.RadioBox(self, choices=['external','internal (MfN)'], majorDimension=1, style=wx.RA_SPECIFY_ROWS)
        if 'server' in data.keys(): self.source.SetSelection(0 if data['server']=="external" else 1)
        flex.Add(self.source)
        flex.Add(wx.StaticText(self, label= ' Username ', style=wx.ALIGN_LEFT))
        self.username = wx.TextCtrl(self, size=(300,-1))
        if 'user' in data.keys(): self.username.SetValue(data['user'])
        flex.Add(self.username)
        flex.Add(wx.StaticText(self, label= ' Password ', style=wx.ALIGN_LEFT))
        self.password = wx.TextCtrl(self, size=(300,-1), style=wx.TE_PASSWORD)
        if 'pw' in data.keys(): self.password.SetValue(data['pw'])
        flex.Add(self.password)
        flex.AddGrowableCol(1)
        hor = Ok_Cancel_Wrapper(self)
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(flex)
        sizer.Add((20,20))
        sizer.Add(hor,0,wx.CENTER)
        sizer.Add((20,20))
        self.SetSizerAndFit(sizer)
        self.Layout()

class ParamDialog(wx.Dialog): # Dialog to choose parameters
    def __init__(self, parent):
        wx.Dialog.__init__(self, parent, -1, 'Enter your requested parameters', size=(400,180), pos=(200,200))
        flex = wx.FlexGridSizer(9,2,5,5)
        flex.Add(wx.StaticText(self, label= ' Source: ', style=wx.ALIGN_LEFT))
        self.source = wx.RadioBox(self, choices=['Database','Files'], majorDimension=1, style=wx.RA_SPECIFY_ROWS)
        flex.Add(self.source)
        flex.Add(wx.StaticText(self, label= ' Show Datum Codes: ', style=wx.ALIGN_LEFT))
        self.show_code = wx.RadioBox(self, choices=['Yes','No'], majorDimension=1, style=wx.RA_SPECIFY_ROWS)
        self.show_code.SetSelection(1)
        flex.Add(self.show_code)
        flex.Add(wx.StaticText(self, label= ' Color Scheme: ', style=wx.ALIGN_LEFT))
        self.color = wx.RadioBox(self, choices=['B&W','Color','Colorfill'], majorDimension=1, style=wx.RA_SPECIFY_ROWS)
        self.color.SetSelection(2)
        flex.Add(self.color)
        flex.Add(wx.StaticText(self, label= ' Plot Paleomag: ', style=wx.ALIGN_LEFT))
        self.show_pmag = wx.RadioBox(self, choices=['Yes','No'], majorDimension=1, style=wx.RA_SPECIFY_ROWS)
        self.show_pmag.SetSelection(1) # Defaults to No
        flex.Add(self.show_pmag)
        flex.Add(wx.StaticText(self, label= ' Set Axes Values: ', style=wx.ALIGN_LEFT))
        self.set_axes = wx.RadioBox(self, choices=['Yes','No'], majorDimension=1, style=wx.RA_SPECIFY_ROWS)
        self.set_axes.SetSelection(1) # Defaults to No
        flex.Add(self.set_axes)
        flex.AddGrowableCol(1)
        hor = Ok_Cancel_Wrapper(self)
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(flex)
        sizer.Add((20,20))
        sizer.Add(hor,0,wx.CENTER)
        sizer.Add((20,20))
        self.SetSizerAndFit(sizer)
        self.Layout()

class AxisDialog(wx.Dialog): # Dialog to set the axes
    def __init__(self,axes):
        wx.Dialog.__init__(self, None, -1, 'Enter New Axis', size=(400,180))
        flex = wx.FlexGridSizer(9,2,5,5)
        flex.Add(wx.StaticText(self, label= ' Youngest Age ', style=wx.ALIGN_LEFT))
        self.xmin = wx.TextCtrl(self, size=(300,-1))
        self.xmin.SetValue(str(axes[0]))
        flex.Add(self.xmin)
        flex.Add(wx.StaticText(self, label= ' Oldest Age ', style=wx.ALIGN_LEFT))
        self.xmax = wx.TextCtrl(self, size=(300,-1))
        self.xmax.SetValue(str(axes[1]))
        flex.Add(self.xmax)
        flex.Add(wx.StaticText(self, label= ' Higher Depth ', style=wx.ALIGN_LEFT))
        self.ymax = wx.TextCtrl(self, size=(300,-1))
        self.ymax.SetValue(str(axes[3]))
        flex.Add(self.ymax)
        flex.Add(wx.StaticText(self, label= ' Lower Depth ', style=wx.ALIGN_LEFT))
        self.ymin = wx.TextCtrl(self, size=(300,-1))
        self.ymin.SetValue(str(axes[2]))
        flex.Add(self.ymin)
        hor = Ok_Cancel_Wrapper(self)
        flex.Add((20,20))
        flex.Add(hor)
        flex.Add((20,20))
        flex.AddGrowableCol(1)
        self.SetSizerAndFit(flex)
        self.Layout()

class LabelDialog(wx.Dialog): # Dialog to set the labels
    def __init__(self,labels):
        wx.Dialog.__init__(self, None, -1, 'Enter New Labels', size=(400,180))
        flex = wx.FlexGridSizer(9,2,5,5)
        flex.Add(wx.StaticText(self, label= ' Title ', style=wx.ALIGN_LEFT))
        self.title = wx.TextCtrl(self, size=(300,-1))
        self.title.SetValue(str(labels[0]))
        flex.Add(self.title)
        flex.Add(wx.StaticText(self, label= ' X axis ', style=wx.ALIGN_LEFT))
        self.xaxis = wx.TextCtrl(self, size=(300,-1))
        self.xaxis.SetValue(str(labels[1]))
        flex.Add(self.xaxis)
        flex.Add(wx.StaticText(self, label= ' Y axis ', style=wx.ALIGN_LEFT))
        self.yaxis = wx.TextCtrl(self, size=(300,-1))
        self.yaxis.SetValue(str(labels[2]))
        flex.Add(self.yaxis)
        flex.AddGrowableCol(1)
        hor = Ok_Cancel_Wrapper(self)
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(flex)
        sizer.Add((20,20))
        sizer.Add(hor,0,wx.CENTER)
        sizer.Add((20,20))
        self.SetSizerAndFit(sizer)
        self.Layout()

class ListEventsFrame(wx.Frame):
    def __init__(self, parent, data):
        wx.Frame.__init__(self, parent, size=(750,500), title="List Events",pos=(300,50))
        orig = 1 if 'origMinAge' in data['dfDATUMS'].columns else 0
        dfLIST = data['dfDATUMS'][['plot_fossil_group', 'datum_type', 'datum_name',
                          'plot_code', 'datum_age_min_ma', 'datum_age_max_ma',
                          'top_depth','bottom_depth', 'plot_age', 'plot_depth',
                          'origMinAge', 'origMaxAge']] if orig else data['dfDATUMS'][['plot_fossil_group', 'datum_type', 'datum_name',
                                            'plot_code', 'datum_age_min_ma', 'datum_age_max_ma',
                                            'top_depth','bottom_depth', 'plot_age', 'plot_depth']]
        dfLIST = dfLIST.sort_values(['plot_fossil_group','top_depth','datum_name'], ascending=[True,False,True])
        self.index = 0
        self.eventList = dfLIST.to_dict('records')
        self.list_ctrl = wx.ListCtrl(self, size=(-1,450), style = wx.LC_REPORT|wx.BORDER_SUNKEN|wx.LC_SINGLE_SEL)
        self.list_ctrl.InsertColumn(0,'plot_fossil_group')
        self.list_ctrl.InsertColumn(1,'datum_type')
        self.list_ctrl.InsertColumn(2,'datum_name')
        self.list_ctrl.InsertColumn(3,'plot_code')
        self.list_ctrl.InsertColumn(4,'datum_age_min_ma')
        self.list_ctrl.InsertColumn(5,'datum_age_max_ma')
        self.list_ctrl.InsertColumn(6,'top_depth')
        self.list_ctrl.InsertColumn(7,'bottom_depth')
        self.list_ctrl.InsertColumn(8,'plot_age')
        self.list_ctrl.InsertColumn(9,'plot_depth')
        if orig:
            self.list_ctrl.InsertColumn(10,'origMinAge')
            self.list_ctrl.InsertColumn(11,'origMaxAge')
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(self.list_ctrl, 0, wx.ALL|wx.EXPAND, 5)
        for i in self.eventList:
            self.list_ctrl.InsertStringItem(self.index, str(i['plot_fossil_group']))
            self.list_ctrl.SetStringItem(self.index, 1, str(i['datum_type']))
            self.list_ctrl.SetStringItem(self.index, 2, str(i['datum_name']))
            self.list_ctrl.SetStringItem(self.index, 3, str(i['plot_code']))
            self.list_ctrl.SetStringItem(self.index, 4, str(i['datum_age_min_ma']))
            self.list_ctrl.SetStringItem(self.index, 5, str(i['datum_age_max_ma']))
            self.list_ctrl.SetStringItem(self.index, 6, str(i['top_depth']))
            self.list_ctrl.SetStringItem(self.index, 7, str(i['bottom_depth']))
            self.list_ctrl.SetStringItem(self.index, 8, str(i['plot_age']))
            self.list_ctrl.SetStringItem(self.index, 9, str(i['plot_depth']))
            if orig:
                self.list_ctrl.SetStringItem(self.index, 10, str(i['origMinAge']))
                self.list_ctrl.SetStringItem(self.index, 11, str(i['origMaxAge']))
            self.index += 1
        hor = wx.BoxSizer(wx.HORIZONTAL)
        exp = wx.Button(self, wx.ID_ANY, "Export to File")
        exp.Bind(wx.EVT_BUTTON, lambda event: self.save_events(event,data))
        hor.Add(exp,0,wx.CENTER)
        sizer.Add(hor,0,wx.CENTER)
        self.SetSizer(sizer)
        self.Show(True)
        #self.Layout()

    def save_events(self,event,data):
        file = data['holeID'] + "_btrat.txt"
        default = os.environ['NSBPATH'] + "/STRAT/"
        wildcard = "Tab-separated files (*.txt)|*.txt"
        dlg = wx.FileDialog(None, 'Save your file', defaultDir =default, defaultFile=file, wildcard=wildcard, style=wx.FD_SAVE)
        if dlg.ShowModal() == wx.ID_OK:
            fileName = dlg.GetPath()
            toScale = data['toScale']
            fo = open(fileName,"w")
            header = "%s\t2\t%s\n" % (data['holeID'],data['toScale'])
            fo.write(header)
            fo.write("GROUP\tNAME\tPLOTCODE\tYOUNG AGE\tOLD AGE\tTOP DEPTH\tBOT DEPTH\n")
            list_data = data['dfDATUMS'].to_dict('records')
            for i in list_data:
                i['datum_age_min_ma'] = str(i['datum_age_min_ma']) if i['datum_age_min_ma'] is not None else ''
                i['datum_age_max_ma'] = str(i['datum_age_max_ma']) if i['datum_age_max_ma'] is not None else ''
                i['top_depth'] = str(i['top_depth']) if i['top_depth'] is not np.nan else ''
                i['bottom_depth'] = str(i['bottom_depth']) if i['bottom_depth'] is not np.nan else ''
                fo.write( "%(plot_fossil_group)s\t%(datum_type)s %(datum_name)s\t%(plot_code)s\t%(datum_age_min_ma)s\t%(datum_age_max_ma)s\t%(top_depth)s\t%(bottom_depth)s\n" % i)
            fo.close()

class ManageLOCs(wx.Dialog):
    def __init__(self, parent, data, locList, locIdx):
        wx.Dialog.__init__(self, parent, -1, size=(-1,-1), title='Manage loaded LOCs', pos=(200,200))
        self.locs = locList
        self.current = locIdx
        self.current_name = data['LOCFileName'][self.current]
        self.finished = True
        sizerTop = wx.BoxSizer(wx.VERTICAL)
        sizer = wx.FlexGridSizer(3+len(self.locs),4,5,5)
        for i,j in enumerate(self.locs):
            locname = data['LOCFileName'][i]
            if '/' in locname: locname = locname[locname.rfind('/')+1:]
            sizer.Add(wx.StaticText(self, label=str(i), style=wx.ALIGN_LEFT))
            sizer.Add(wx.StaticText(self, label=locname, style=wx.ALIGN_LEFT))
            if i==self.current:
                sizer.Add(wx.StaticText(self, label="[Current LOC]", style=wx.ALIGN_LEFT))
                sizer.Add((20,20))
            else:
                d = wx.Button(self,wx.ID_ANY,label="Set as Current", name=str(i))
                d.Bind(wx.EVT_BUTTON, self.SetCurrent)
                sizer.Add(d)
                b = wx.Button(self,wx.ID_ANY, label='Delete', name=str(i))
                b.Bind(wx.EVT_BUTTON, self.Delete)
                sizer.Add(b)
        sizerTop.Add(sizer)
        if len(self.locs)>1:
            sizerTop.Add((20,20))
            hor = wx.BoxSizer(wx.HORIZONTAL)
            if len(data['phantom']):
                hor.Add(wx.StaticText(self, label="Current comparison: LOC %i vs LOC %i" % (self.current, data['phantom']['locIdx']), style=wx.ALIGN_RIGHT))
                bt = wx.Button(self,wx.ID_ANY, label="Cancel")
                bt.Bind(wx.EVT_BUTTON, self.CancelCompare)
                hor.Add(bt)
            else:
                hor.Add(wx.StaticText(self, label="Compare current LOC with LOC n°", style=wx.ALIGN_RIGHT))
                other_loc = [str(k) for k in xrange(len(self.locs)) if k != self.current]
                self.roll = wx.ComboBox(self, id=wx.ID_ANY, size=(-1,-1), choices= other_loc, style=wx.CB_READONLY|wx.CB_DROPDOWN)
                hor.Add(self.roll)
                bt = wx.Button(self,wx.ID_ANY, label="Compare")
                bt.Bind(wx.EVT_BUTTON, self.Compare)
                hor.Add(bt)
            sizerTop.Add(hor, 0, wx.CENTER)
        sizerTop.Add((20,20))
        hor2 = wx.BoxSizer(wx.HORIZONTAL)
        okButton = wx.Button(self, wx.ID_OK, "OK")
        hor2.Add(okButton)
        sizerTop.Add(hor2, 0, wx.CENTER)
        sizerTop.Add((20,20))
        self.SetSizerAndFit(sizerTop)
        self.Layout()

    def CancelCompare(self,event):
        self.finished = False
        data['phantom'] = {}
        self.Close()

    def Compare(self,event):
        self.finished = True
        k = int(self.roll.GetCurrentSelection())
        loc_name = data['LOCFileName'][k]
        if '/' in loc_name: loc_name = loc_name[loc_name.rfind('/')+1:]
        data['phantom'] = {'loc': self.locs[k], 'loc_name': loc_name, 'locIdx': k}
        self.Close()

    def SetCurrent(self,event):
        button = event.GetEventObject()
        k = int(button.GetName())
        self.current = k
        self.finished = False
        self.Close()

    def Delete(self, event):
        button = event.GetEventObject()
        k = int(button.GetName())
        self.locs.pop(k)
        data['LOCFileName'].pop(k)
        self.current = [i for i, k in enumerate(data['LOCFileName']) if k==self.current_name][0]
        self.finished = False
        self.Close()

class LOCFrame(wx.Frame):
    def __init__(self, parent, x,y):
        wx.Frame.__init__(self, parent, size=(200,400), title="Inspect LOC",pos=(300,50))
        self.index = 0
        self.list_ctrl = wx.ListCtrl(self, size=(-1,400), style = wx.LC_REPORT|wx.BORDER_SUNKEN)
        self.list_ctrl.InsertColumn(0,'Age')
        self.list_ctrl.InsertColumn(1,'Depth')
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(self.list_ctrl, 0, wx.ALL|wx.EXPAND, 5)
        for i in xrange(len(x)):
            self.list_ctrl.InsertStringItem(self.index, '%.3f' % (x[i],))
            self.list_ctrl.SetStringItem(self.index, 1, '%.2f' % (y[i],))
            self.index += 1
        self.SetSizer(sizer)
        self.Show(True)

class ADPFrame(wx.Frame):
    def __init__(self, parent, data):
        wx.Frame.__init__(self, None, -1, 'Age-Depth Plot', size=(500, 300), pos= (550, 50))
        self.messageboard = parent.messageboard
        data['plotGroups'] = get_plot_groups(data['dfDATUMS'],data['plotCodes'])
        # Setup axes
        self.axes = self.process_axes(data)
        self.xMin = max(self.axes[0],0)
        self.xMax = self.axes[1]
        self.yMin = self.axes[2]
        self.yMax = self.axes[3]
        # Plot
        self.has_grid = False
        self.fig = plt.figure()
        self.messageboard.WriteText('plotting...\n')
        self.canvas = FigureCanvas(self, -1, self.fig)
        #Prepare LOC
        self.locList = []
        locData = []
        data['phantom'] = {}
        if len(data['dfLOC']) == 0:
            locData = [(self.xMin,self.yMin),(self.xMax,self.yMax)]
        else:
            for i in range(0,len(data['dfLOC'])):
                locData.append((data['dfLOC']['age_ma'][i], data['dfLOC']['depth_mbsf'][i]))
        self.locList.append(list(locData))
        self.locIdx = 0
        data['LOCFileName'] = [data['LOCFileName'],]
        # Instantiate many variables
        self.showverts = True
        self.showHiatus = True
        self.epsilon = 5
        # Initialize for use later
        self.color = 'g'
        self.linestyle = '-'
        self.linewidth = 1
        self.hcolor = 'r'
        self.hlinestyle = ':'
        self.hlinewidth = 2.5
        self.hLines = []
        # For 'e' - Edit Labels
        data['title'] = 'Age Depth Plot for Site ' + data['holeID']
        data['xAxisLabel'] = 'Age (Ma) '+ data['toScale']
        data['yAxisLabel'] = 'Depth (mbsf)'
        if data['plotColorType'] == 1:
            self.color = 'k'
            self.linestyle = '--'
        else:
            self.color = 'g'
            self.linestyle = '-'
        self.keymap = {'save':'', 'xscale':'', 'yscale':'', 'zoom':'', 'pan':'', 'home':''}
        self.replot(data, self.axes)
        # Plot line of correlation
        # Setup index for pick of a vertex
        self._ind = None
        # Setup callbacks
        self.canvas.mpl_connect('draw_event', self.draw_callback)
        self.canvas.mpl_connect('button_press_event', self.button_press_callback)
        self.canvas.mpl_connect('button_release_event', self.button_release_callback)
        self.canvas.mpl_connect('motion_notify_event', self.motion_notify_callback)
        self.canvas.mpl_connect('key_press_event', self.key_press_callback)
        # Setup Status bar, toolbar and sizers
        self.statusBar = wx.StatusBar(self, -1)
        self.SetStatusBar(self.statusBar)
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.Add(self.canvas, 1, wx.LEFT | wx.TOP | wx.EXPAND)
        self.SetSizer(self.sizer)
        self.Fit()
        # Setup menubar
        self.menubar = ADP_Menubar(self)
        Save = wx.Menu()
        Save1 = Save.Append(wx.ID_ANY, 'Save Plot')
        Save2 = Save.Append(wx.ID_ANY, 'Save LOC')
        Save3 = Save.Append(wx.ID_ANY, 'Inspect LOC')
        Save4 = Save.Append(wx.ID_ANY, 'Inspect Stratigraphic data')
        Save5 = Save.Append(wx.ID_ANY, 'Project events on LOC')
        Save.AppendSeparator()
        Plot1 = Save.Append(wx.ID_ANY, 'Add Stratigraphic events from file')
        Plot2 = Save.Append(wx.ID_ANY, 'Load a new LOC')
        Plot3 = Save.Append(wx.ID_ANY, 'Manage loaded LOCs')
        self.menubar.Append(Save, 'Plot')
        self.Bind(wx.EVT_MENU, lambda event: save_plot(self, data['holeID'], self.fig), Save1)
        self.Bind(wx.EVT_MENU, lambda event: save_loc(self, data['holeID'], self.line.get_data()[0], self.line.get_data()[1]), Save2)
        self.Bind(wx.EVT_MENU, lambda event: self.inspect_loc(self.line.get_data()[0], self.line.get_data()[1]), Save3)
        self.Bind(wx.EVT_MENU, lambda event: self.list_events(data), Save4)
        self.Bind(wx.EVT_MENU, lambda event: project_events(self,data,self.line.get_data()[0], self.line.get_data()[1]), Save5)
        self.Bind(wx.EVT_MENU, lambda event: self.add_events(event,data), Plot1)
        self.Bind(wx.EVT_MENU, lambda event: self.add_loc(event,data), Plot2)
        self.Bind(wx.EVT_MENU, lambda event: self.manage_loc(event,data), Plot3)
        self.SetMenuBar(self.menubar)
        self.Show(True)

    def manage_loc(self,event,data):
        m = ManageLOCs(None, data, self.locList, self.locIdx)
        if m.ShowModal() == wx.ID_OK:
            self.locList = m.locs
            self.locIdx = m.current
            if m.finished:
                self.replot(data,self.axes)
            else:
                self.manage_loc(event,data)

    def add_loc(self,event,data):
        fd = FileOrDbDialog(None)
        newLOC = []
        if fd.ShowModal() == wx.ID_OK:
            source = fd.source.GetStringSelection()
            if source == 'NSB Database':
                db_login = dbDialog(self,data) # Open DB Connexion dialog window
                if db_login.ShowModal() == wx.ID_OK: # When OK clicked:
                    # Collect and save data entered, for later connexions
                    data['server'] = db_login.source.GetStringSelection()
                    server = "212.201.100.111" if data['server'] == "external" else "192.168.101.133"
                    data['user'] = db_login.username.GetValue()
                    data['pw'] = db_login.password.GetValue()
                    theEngine = "postgresql://%s:%s@%s/nsb" % (data['user'],data['pw'],server)
                    engine = None
                    try: # Try to connect
                        engine = create_engine(theEngine,client_encoding='latin1')
                        engine.connect()
                    except: # If unsuccessfull, say so and go back to Welcome window.
                        self.messageboard.WriteText('Login failed.\n')
                        return
                    if engine is not None:
                        sqlHOLE = "SELECT hole_id FROM neptune_hole_summary WHERE site_hole='%s';" % (data['holeID'],)
                        hole_id = psql.read_sql_query(sqlHOLE,engine)
                        hole_id = hole_id['hole_id'][0]
                        if len(hole_id)<len(data['holeID']): self.messageboard.WriteText('hole_id %s doesn\'t exist in NSB.\n' % (hole_id,))
                        newLOC = query_loc(engine,hole_id)
                        newLOCname = "NSB revision %i" % (newLOC['revision_no'][0])
            elif source == 'Local File':
                default = os.environ['NSBPATH'] + "/LOC/"
                wildcard = "Tab-separated files (*.txt)|*.txt"
                dlg = wx.FileDialog(None, 'Choose file', defaultDir =default, wildcard=wildcard, style=wx.FD_OPEN)
                if dlg.ShowModal() == wx.ID_OK:
                    fileName = dlg.GetPath()
                    newLOC = read_loc(self,fileName, data)
                    newLOCname = fileName
            if len(newLOC):
                data['dfLOC'] = newLOC
                locData = []
                if len(data['dfLOC']) == 0:
                    locData = [(self.xMin,self.yMax),(self.xMax,self.yMin)]
                else:
                    for i in range(0,len(data['dfLOC'])):
                        locData.append((data['dfLOC']['age_ma'][i], data['dfLOC']['depth_mbsf'][i]))
                self.locList.append(list(locData))
                self.locIdx = len(self.locList) - 1
                data['LOCFileName'].append(newLOCname)
                axes = self.process_axes(data)
                self.replot(data,axes)
            else: return
        else: return

    def add_events(self, event, data):
        default = os.environ['NSBPATH'] + "/STRAT/"
        wildcard = "Tab-separated files (*.txt)|*.txt"
        dlg = wx.FileDialog(None, 'Choose file', defaultDir =default, wildcard=wildcard, style=wx.FD_OPEN)
        if dlg.ShowModal() == wx.ID_OK:
            fileName = dlg.GetPath()
            new_data = read_datums(self,fileName, data)
            r = csv.reader(open(fileName,'rU'),delimiter='\t')
            n = 0
            for row in r:
                if n == 0 :
                    fromScale = row[2]
                    n = 1
                else: pass
            data['stratFileName'] += " + " + os.path.basename(fileName)
            new_data = convert_agescale_file(data['toScale'], fromScale, data['dfGPTS'], new_data)
            data['dfDATUMS'] = pd.concat([data['dfDATUMS'],new_data], ignore_index=True)
            axes = self.process_axes(data)
            self.replot(data, axes)

    def replot(self,data,axes):
        plt.clf()
        plt.grid(self.has_grid) #Set grid or not depending on value of self.has_grid
        plt.minorticks_on()
        # Plot
        self.xMin = max(axes[0],0)
        self.xMax = axes[1]
        self.yMin = axes[2]
        self.yMax = axes[3]
        self.ax = self.fig.add_subplot(111)
        self.ax.set_xlim([self.xMin,self.xMax])
        self.ax.set_ylim([self.yMax + (abs(self.yMax - self.yMin) * .05), self.yMin - (abs(self.yMax - self.yMin) * 0.05)])
        self.ax.tick_params(direction='out', which='both', right='off', top='off', width=2)
        #Plotting
        plt.rc('grid', linestyle=':', color='#7f7f7f', alpha=1) #Grid customization
        plt.rc('keymap', **self.keymap)
        self.ax.set_axisbelow(True) #So that the grid is below the main elements
        if len(data['phantom']):
            xp, yp = zip(*data['phantom']['loc'])
            col_phantom = "#0000FF99" if self.color == 'g' else "#BEBEBE99"
            self.ax.plot(xp, yp, color=col_phantom, linestyle=self.linestyle, linewidth=self.linewidth, animated=False)
        if len(data['dfDATUMS']):
            plot_datums(data,self.fig, self.ax, self.canvas)
        if len(data['dfCORES']):
            plot_cores(data['dfCORES'], self.xMin, self.xMax, self.yMin, self.yMax)
        if len(data['dfTIME']):
            plot_time_scale(data['dfTIME'], self.xMin, self.xMax, self.yMin, self.yMax)
        if len(data['dfCHRONS']):
            plot_chrons(data['dfCHRONS'], self.xMin, self.xMax, self.yMin, self.yMax)
        if 'dfPMAGS' in data.keys():
            plot_paleomag_interval(data['dfPMAGS'], self.xMin, self.xMax, self.yMin, self.yMax)
        plt.xlabel(data['xAxisLabel'])
        plt.ylabel(data['yAxisLabel'])
        plt.title(data['title'])
        x, y = zip(*self.locList[self.locIdx])
        self.hLines = []
        self.line, = self.ax.plot(x, y, marker='s', markerfacecolor=self.color, color=self.color,
                                  linestyle=self.linestyle, linewidth=self.linewidth, markersize=3, animated=False)
        self.plot_hiatuses()
        plot_metadata(self, self.xMin, self.xMax, self.yMin, self.yMax, data)
        # Setup index for pick of a vertex
        self.canvas.draw()

    def draw_callback(self, event):
        self.background = self.canvas.copy_from_bbox(self.ax.bbox)
        self.ax.draw_artist(self.line)
        self.canvas.blit(self.ax.bbox)

    def get_ind_under_point(self, event):
        """Get the index of the vertex under point if within epsilon tolerance."""
        # Display coordinates
        xy = np.asarray(zip(*self.line.get_data()) )
        xyt = self.line.get_transform().transform(xy)
        xt, yt = xyt[:, 0], xyt[:, 1]
        d = np.sqrt((xt-event.x)**2 + (yt-event.y)**2)
        ind = d.argmin()
        if event.key == 'i':  # Insert
            return ind
        if event.key == 'd':  # Delete
            if d[ind] >= self.epsilon:  # Check within epsilon distance
                ind = None
            return ind
        if event.button:  # DEV: make a point was selected
            if d[ind] > self.epsilon:
                ind = None

        return ind

    def button_press_callback(self, event):
        """Whenever a mouse button is pressed."""
        if not self.showverts: return
        if event.inaxes == None: return
        if event.button != 1: return
        self._ind = self.get_ind_under_point(event)

    def button_release_callback(self, event):
        """Whenever a mouse button is released."""
        if not self.showverts: return
        if event.button != 1: return
        # Check for a vertex/point was moved
        if self._ind is None: return
        self._ind = None
        # Moved a vertex/point - make a new LOC
        x, y = self.line.get_data()
        new = data['LOCFileName'][self.locIdx] != 'modified'
        self.mod_loc(x, y, new) # add a new LOC to locList

    def key_press_callback(self, event):
        """Whenever a key is pressed."""
        if not event.inaxes:
            return

        if event.key == 't': # Toggle visibility of the line
            self.showverts = not self.showverts
            self.line.set_visible(self.showverts)
            if not self.showverts: self._ind = None
            self.showHiatus = not self.showHiatus # Toggle hiatuses
            for i in range (0,len(self.hLines)):
                self.hLines[i][0].set_visible(self.showHiatus)
            self.canvas.draw()

        elif event.key =='i': # Insert a vertex to the line
            is_valid = 0 # reset every time ...
            ind = self.get_ind_under_point(event)
            x, y = self.line.get_data()
            if not type(x) is list: # First time convert np.array to list
                x = x.tolist()
                y = y.tolist()
            if event.xdata > x[ind]: # Check to adjust ind for insert position
                ind = ind + 1
            # Determine if valid position and insert or append vertex
            if event.xdata > x[len(x)-1] and event.ydata >= y[len(y)-1]:
                # Append after last point
                x.append(event.xdata)
                y.append(event.ydata)
                is_valid = 1
            elif event.xdata < x[0] and event.ydata <= y[0]:
                # Insert before first point
                x.insert(0, event.xdata)
                y.insert(0, event.ydata)
                is_valid = 1
            elif ind <= (len(x)-1) and event.xdata < x[ind] and event.ydata <= y[ind] and event.xdata > x[ind-1] and event.ydata > y[ind-1]:
                # Insert point
                x.insert(ind, event.xdata)
                y.insert(ind, event.ydata)
                is_valid = 1

            if is_valid: # was it a valid insert?
                new = data['LOCFileName'][self.locIdx] != 'modified'
                self.mod_loc(x, y, new) # add a new LOC to locList

        elif event.key == 'd': # Delete a vertex of the line
            ind = self.get_ind_under_point(event)
            if ind is not None:
                x, y = self.line.get_data()
                if not type(x) is list:
                    x = x.tolist()
                    y = y.tolist()
                # Remove x and y from list at ind
                x.pop(ind)
                y.pop(ind)
                new = data['LOCFileName'][self.locIdx] != 'modified'
                self.mod_loc(x, y, new) # add a new LOC to locList

        elif event.key == 's': # Save LOC to file
            x, y = self.line.get_data()
            save_loc(self, data['holeID'], x, y)

        elif event.key == 'I': # Inspect LOC
            x, y = self.line.get_data()
            self.inspect_loc(x, y)

        elif event.key == 'p': # Save plot to file
            save_plot(self, data['holeID'], self.fig)

        elif event.key == 'l':  # List events
            self.list_events(data)

        elif event.key == 'c': # Project events
            x, y = self.line.get_data()
            project_events(self,data, x, y)

        elif event.key == 'a': # Set axes
            axes = [self.xMin,self.xMax,self.yMin,self.yMax]
            newAxes = set_axes(self,axes)
            self.xMin, self.xMax, self.yMin, self.yMax = newAxes
            self.messageboard.WriteText('new axis:\nxMin=%.2f, xMax=%.2f, yMin=%.2f, yMax=%.2f\n' % (self.xMin, self.xMax, self.yMin, self.yMax))
            self.replot(data,newAxes)

        elif event.key == 'g':
            self.has_grid = not self.has_grid
            self.replot(data,[self.xMin,self.xMax,self.yMin,self.yMax])

        elif event.key == 'e': # Edit title and/or axes labels
            labels = set_labels([data['title'],data['xAxisLabel'],data['yAxisLabel']])
            data['title'], data['xAxisLabel'], data['yAxisLabel']  = labels
            plt.title(data['title'])
            plt.xlabel(data['xAxisLabel'])
            plt.ylabel(data['yAxisLabel'])
            self.canvas.draw()

        elif event.key == 'h': # Program Help
            self.GenericHelp(event)

        elif event.key == 'x': # Exit
            self.Quit(event)

        elif event.key == 'N' and self.locIdx < (len(self.locList)-1):  # Next LOC in locList
            self.locIdx = self.locIdx + 1
            self.replot(data,self.axes)

        elif event.key == 'P' and self.locIdx > 0:  # Previous LOC in locList
            self.locIdx = self.locIdx - 1
            self.replot(data,self.axes)

    def motion_notify_callback(self,event):
        '''on mouse movement'''
        if event.inaxes: self.statusBar.SetStatusText(("x= %.3f y=%.2f"%(event.xdata,event.ydata)), 0)
        if not self.showverts: return
        if self._ind is None: return
        if event.inaxes is None: return
        if event.button != 1: return
        x,y = self.line.get_data()
        if not type(x) is list:
            x = x.tolist()
            y = y.tolist()

        # DEV: determine boundaries for moving a point
        # DEV: first point, make xBounds to x axis min, y axis max
        # DEV: modified code from Neptune ADP (Java)...
        if self._ind == 0:
            xBound0 = self.xMin
            yBound0 = self.yMin
        else:
            # Previous point
            xBound0 = x[self._ind - 1]
            yBound0 = y[self._ind - 1]

        if self._ind == len(x) - 1: # Last point
            xBound1 = self.xMax
            yBound1 = self.yMax
        else:
            xBound1 = x[self._ind + 1] # Next point
            yBound1 = y[self._ind + 1]

        # Don't exceed x boundaries
        if event.xdata < xBound0:
            event.xdata = xBound0
        elif event.xdata > xBound1:
            event.xdata = xBound1

        # Don't exceed y boundaries
        if event.ydata < yBound0:
            event.ydata = yBound0
        elif event.ydata > yBound1:
            event.ydata = yBound1

        x[self._ind] = event.xdata
        y[self._ind] = event.ydata

        self.line.set_data(x, y)

        x, y = self.line.get_data()

        self.canvas.restore_region(self.background)
        self.ax.draw_artist(self.line)
        self.canvas.blit(self.ax.bbox)

        # Plot hiatuses
        self.plot_hiatuses()

        # Re-draw for hiatuses
        self.canvas.draw()

    def plot_hiatuses(self):
        """Plot LOC hiatuses."""

        # Remove current hiatus lines
        for i in range(0,len(self.hLines)):
            self.ax.lines.remove(self.hLines[i][0])
        # Set or reset hiatus lines
        self.hLines = []

        # Get the current LOC to test for hiatuses
        x, y = self.line.get_data()
        if not type(x) is list: # First time convert np.array to list
            x = x.tolist()
            y = y.tolist()

        # Check for hiatuses and plot
        for i in range (0,len(x)-1): # Check x(age) at different y(depth)
            if (abs(y[i+1])-abs(y[i]) == 0.) or (abs(y[i+1])-abs(y[i]))/(x[i+1]-x[i]) <= 0.5: # <=0.5meter/ma accumulation
                xh = [x[i], x[i+1]]
                yh = [y[i], y[i+1]]

                self.hlinewidth = 2.5

                if data['plotColorType'] == 1: # Black & White plot
                    self.hcolor = 'k'
                    self.hlinestyle = ':'
                else: # Color plot
                    self.hcolor = 'r'
                    self.hlinestyle = ':'
                if y[i] != y[i+1]: # Almost a hiatus - alert user
                    N = self.messageboard.GetNumberOfLines()
                    if 'hiatus' not in self.messageboard.GetLineText(N-2): #Don't spam the user with same alert
                        self.messageboard.WriteText('alert - to make a hiatus adjust point to same depth\n')
                    self.hlinestyle = '-.'
                    self.hlinewidth = 12.

                # Plot and save line to list
                self.hLines.append(self.ax.plot(xh, yh, marker='s',
                                   markerfacecolor=self.hcolor, color=self.hcolor,
                                   linestyle=self.hlinestyle, linewidth=self.hlinewidth))

    def mod_loc(self,x, y, new):
        """Adding a LOC to list of LOC's."""
        newLoc =[]
        for i in range(0,len(x)):
            newLoc.append((x[i], y[i]))
        if new:
            self.locIdx = len(self.locList)
            self.locList.append(list(newLoc))
            data['LOCFileName'].append('modified')
            self.replot(data,self.axes)
        else:
            self.locList[self.locIdx] = list(newLoc)
            self.redraw_loc()

    def redraw_loc(self):
        self.ax.lines.remove(self.line) # remove the line currently plotting
        x, y = zip(*self.locList[self.locIdx]) # create a new line with inserted point
        self.line, = self.ax.plot(x, y, marker='s', markerfacecolor=self.color, color=self.color, linestyle=self.linestyle, linewidth=self.linewidth, markersize=3, animated=False)
        self.plot_hiatuses()
        self.canvas.draw()

    def list_events(self,data): #Rewritten
        w = ListEventsFrame(None, data)

    def inspect_loc(self,x,y): #Rewritten
        w = LOCFrame(None, x, y)

    def Quit(self,event):
        self.messageboard.WriteText('closing plot\n')
        self.Close()

    def GenericHelp(self, event):
        filename = os.environ['NSBPATH'] + '/REF/manual.pdf'
        if sys.platform == "win32":
            os.startfile(filename)
        else:
            opener ="open" if sys.platform == "darwin" else "xdg-open"
            subprocess.call([opener, filename])

    def process_axes(self, data): # Process data to configure axes. Mostly untouched from Pat's code
        ages = data['dfDATUMS']['datum_age_max_ma'].tolist()
        depths = data['dfDATUMS']['top_depth'].tolist()
        if len(data['dfLOC']):
            ages = ages + data['dfLOC']['age_ma'].tolist()
            depths = depths + data['dfLOC']['depth_mbsf'].tolist()
        if len(data['dfCORES']):
            depths = depths + data['dfCORES']['top_depth'].tolist()
            depths = depths + data['dfCORES']['bottom_depth'].tolist()
        xMin = math.floor(min(x for x in ages if x is not None)/10.)*10
        xMax = math.ceil(max(ages)/10.)*10
        yMin = math.floor(min(x for x in depths if x is not None)/10.)*10
        yMax = math.ceil(max(depths)/10.)*10
        if xMax-max(ages) > 5.: xMax = xMax - 5.
        axes = [xMin, xMax, yMin, yMax]
        self.messageboard.WriteText('calculated axis:\nxMin=%.2f, xMax=%.2f, yMin=%.2f, yMax=%.2f\n' % (xMin, xMax, yMin, yMax))
        if data['setAxes'] == 1:
            newAxes = set_axes(self,axes)
            xMin = float(newAxes[0])
            xMax = float(newAxes[1])
            yMin = float(newAxes[2])
            yMax = float(newAxes[3])
            axes = []
            axes.append(xMin)
            axes.append(xMax)
            axes.append(yMin)
            axes.append(yMax)
            self.messageboard.WriteText('user set axis:\nxMin=%.2f, xMax=%.2f, yMin=%.2f, yMax=%.2f\n' % (xMin, xMax, yMin, yMax))
        return axes

#Main Frame:
class WelcomeFrame(wx.Frame):
    def __init__(self, parent,data):
        wx.Frame.__init__(self, parent, size= (400,500), title="Welcome to NSB-ADP", pos=(50,50))
        self.menubar = ADP_Menubar(self) # Create menubar
        self.SetMenuBar(self.menubar) # Instantiate menubar
        sizer = wx.BoxSizer(wx.VERTICAL)
        okButton = wx.Button(self, wx.ID_OK, "Start an Age-Depth Plot")
        okButton.Bind(wx.EVT_BUTTON, self.Run)
        sizer.Add(okButton,1,wx.CENTER)
        self.messageboard = wx.TextCtrl(self,size=(400,400),value="",style=wx.TE_READONLY|wx.TE_MULTILINE|wx.HSCROLL)
        sizer.Add(self.messageboard, 1, wx.CENTER) # Message to user will be displayed on messageboard
        outer = wx.BoxSizer(wx.HORIZONTAL)
        outer.Add(sizer,1,wx.Center)
        self.SetSizer(outer)

    def Quit(self,event):
        self.Close()

    def GenericHelp(self, event):
        filename = os.environ['NSBPATH'] + '/REF/manual.pdf'
        if sys.platform == "win32":
            os.startfile(filename)
        else:
            opener ="open" if sys.platform == "darwin" else "xdg-open"
            subprocess.call([opener, filename])

    def Run(self,event):
        params = ParamDialog(self) #Open Parameter dialog window
        data['toScale'] = 'Grad12' # Default scale
        data['dfGPTS'] = read_gpts(self)
        if params.ShowModal() == wx.ID_OK: # Do, when OK clicked:
            # Collect parameters:
            data['plotCodes'] = 1 if params.show_code.GetStringSelection()=="Yes" else 0
            color = params.color.GetStringSelection()
            if color == "B&W":
                data['plotColorType'] = 1
            elif color == "Color":
                data['plotColorType'] = 2
            else:
                data['plotColorType'] = 3
            data['plotPMAG'] = 1 if params.show_pmag.GetStringSelection()=="Yes" else 0
            data['setAxes'] = 1 if params.set_axes.GetStringSelection()=="Yes" else 0
            if params.source.GetStringSelection() == "Database":
                db_login = dbDialog(self,data) # Open DB Connexion dialog window
                if db_login.ShowModal() == wx.ID_OK: # When OK clicked:
                    # Collect and save data entered, for later connexions
                    data['server'] = db_login.source.GetStringSelection()
                    server = "212.201.100.111" if data['server'] == "external" else "192.168.101.133"
                    data['user'] = db_login.username.GetValue()
                    data['pw'] = db_login.password.GetValue()
                    theEngine = "postgresql://%s:%s@%s/nsb" % (data['user'],data['pw'],server)
                    engine = None
                    try: # Try to connect
                        engine = create_engine(theEngine,client_encoding='latin1')
                        engine.connect()
                    except: # If unsuccessfull, say so and go back to Welcome window.
                        self.messageboard.WriteText('Login failed.\n')
                        return
                    if engine is not None: # If successfull, proceed
                        hole = HoleQueryDialog(self, engine) # Open hole query dialog window
                        if hole.ShowModal() == wx.ID_OK: # When OK clicked:
                            # Acknowledge selection and query DB accordingly
                            sel = hole.list_ctrl.GetFirstSelected()
                            data['holeID'] = hole.holeList[sel]['hole_id']
                            data['dfDATUMS'] = query_events(engine, data)
                            data['dfCORES']  = query_cores(engine, data['holeID'])
                            data['dfLOC'] = query_loc(engine,data['holeID'])
                            data['dfPMAGS'] = query_paleomag_interval(engine,data['holeID'])
                            data['holeID'] = re.split('_',data['holeID'])[1]
                            data['dfDATUMS'] = convert_agescale_DB(data)
                            data['stratFileName'] = "NSB"
                            data['LOCFileName'] = "NSB revision %i" % (data['dfLOC']['revision_no'][0]) if len(data['dfLOC']) else ""
                        else: return
                else: return
            else: # If data taken from files
                files = GetFilesDialog(self, data= data) # Open the file selection dialog window
                if files.ShowModal() == wx.ID_OK: # When OK clicked, read those files accordingly
                    data['user'] = files.user.GetValue()
                    data['stratFileName'] = files.stratfile.GetValue()
                    data['dfCORES'] = read_cores(self,files.corefile.GetValue(), data)
                    data['dfDATUMS'] = read_datums(self, data['stratFileName'], data)
                    if data['plotPMAG'] == 1: data['dfPMAGS'] = read_paleomag_interval(self,files.pmagfile.GetValue())
                    data['LOCFileName'] = files.locfile.GetValue()
                    if data['LOCFileName'] != "":
                        data['dfLOC'] = read_loc(self,data['LOCFileName'], data)
                    else:
                        data['dfLOC'] = []
                else: return
        else: return
        data['dfTIME'] = read_time_scale(self,data['toScale'])
        data['dfCHRONS'] = read_paleomag_scale(self,data['toScale'])
        if 'fromScale' in data.keys():
            if data['fromScale'] != data['toScale']:
                data['dfDATUMS'] = convert_agescale_file(data['toScale'], data['fromScale'], data['dfGPTS'], data['dfDATUMS'])
        self.holeID = data['holeID']
        self.messageboard.WriteText('\nHole: %s\n' % data['holeID']) # Summarize data to be plotted
        self.messageboard.WriteText('Number of events: %s\n' % len(data['dfDATUMS']))
        self.messageboard.WriteText('Number of tiepoints: %s\n\n' % len(data['dfLOC']))
        w = ADPFrame(self,data) # Go on and plot

if __name__ == '__main__':
    #Change default of matplotlib and pandas:
    if matplotlib.__version__[0]=='2': matplotlib.style.use('classic')
    matplotlib.rcParams['figure.figsize'] = 11,8
    matplotlib.rcParams['legend.numpoints'] = 2
    matplotlib.rcParams['legend.fontsize'] = 'small'
    matplotlib.rcParams['savefig.dpi'] = 400
    pd.options.mode.chained_assignment = None
    # Find appropriate path to folders:
    if getattr(sys, 'frozen', False):
        if re.search('/Contents/',sys.executable):
            os.environ['NSBPATH'] = os.path.dirname(re.sub('/Contents/.+','',sys.executable))
        else:
            os.environ['NSBPATH'] = os.path.dirname(sys.executable)
    else:
        os.environ['NSBPATH'] = os.path.dirname(os.path.realpath(__file__))
    data = {} # This dictionary will contain every single 'global' variable and pass them around frames, dialogs & functions
    adp = wx.App(False) # Instantiate software
    frame = WelcomeFrame(None, data) # Open main frame
    frame.Show()
    adp.MainLoop() # Loop
