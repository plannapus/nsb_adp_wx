# -*- coding: utf-8 -*-
import os, sys
import decimal, string, datetime, tempfile
import re, math
from bisect import bisect_left
import csv

import numpy as np
import pandas as pd
import pandas.io.sql as psql
from sqlalchemy import create_engine, exc

import wx, wx.html

import matplotlib
matplotlib.use('wxAgg')
import matplotlib.pyplot as plt
from matplotlib.backends.backend_wxagg import FigureCanvasWxAgg as FigureCanvas
from matplotlib.backends.backend_wx import NavigationToolbar2Wx
from matplotlib.figure import Figure

# QUERY_ functions
def query_loc(engine,holeID): #Work
    """Query LOC from database."""
    # Query statement
    sqlLOC = """
        SELECT leg,site,hole,hole_id,a.site_hole,age_ma,depth_mbsf * -1.
        AS depth_mbsf,longitude,latitude
        FROM neptune_hole_summary a, neptune_age_model b
        WHERE a.site_hole = b.site_hole
        AND (b.site_hole,revision_no) IN (
        SELECT site_hole,max(revision_no)
        FROM neptune_age_model
        GROUP BY 1)
        AND hole_id = '%s';
    """ % (holeID,)
    # Use Pandas to run query and retrieve a dataframe of the sql results
    dfLOC = psql.read_sql_query(sqlLOC, engine)
    return dfLOC

def query_events(engine,data): #Work
    """Query events from tables in NSB Berlin database."""
    holeID = data['holeID']
    toScale = data['toScale']
    sqlDATUM = """
        SELECT top_hole_id AS hole_id,event_group AS fossil_group,
        event_group AS plot_fossil_group,
        event_name AS datum_name,event_type AS datum_type,
        plotcode AS plot_code,
        CASE
            WHEN old_age_ma IS NULL THEN
                young_age_ma
            ELSE
                old_age_ma
        END AS datum_age_max_ma,
        CASE
            WHEN young_age_ma IS NULL THEN
                old_age_ma
            ELSE
                young_age_ma
        END AS datum_age_min_ma,
        CASE
            WHEN bottom_depth_mbsf IS NOT NULL THEN
                bottom_depth_mbsf * -1.
            WHEN sample_bottom IS NOT NULL THEN
                neptuneCoreDepth(top_hole_id,sample_bottom) * -1.
            ELSE
                -9999.
        END AS bottom_depth,
        CASE
            WHEN top_depth_mbsf IS NOT NULL THEN
                top_depth_mbsf * -1.
            WHEN sample_top IS NOT NULL THEN
                neptuneCoreDepth(top_hole_id,sample_top) * -1.
            ELSE
                -9999.
            END AS top_depth,
        calibration_scale AS scale,
        calibration_year,event_extent,a.event_id,event_synon_to,bottom_hole_id
        FROM neptune_event a, neptune_event_calibration b, neptune_event_def c
        WHERE a.event_id = b.event_id
        AND b.event_id = c.event_id
        AND top_hole_id = '""" + holeID + """'
        AND (a.event_id,calibration_year) IN (
        SELECT DISTINCT event_id,MAX(calibration_year)
        AS calibration_year
        FROM neptune_event_calibration
        GROUP BY event_id)
        UNION
        SELECT top_hole_id,event_group AS fossil_group,
        event_group AS plot_fossil_group,
        event_name AS datum_name,event_type AS datum_type,
        plotcode AS plot_code,
        age_ma AS datum_age_max_ma,
        age_ma AS datum_age_min_ma,
        CASE
            WHEN bottom_depth_mbsf IS NOT NULL THEN
                bottom_depth_mbsf * -1.
            WHEN sample_bottom IS NOT NULL THEN
                neptuneCoreDepth(top_hole_id,sample_bottom) * -1.
            ELSE
                -9999.
        END AS bottom_depth,
        CASE
            WHEN top_depth_mbsf IS NOT NULL THEN
                top_depth_mbsf * -1.
            WHEN sample_top IS NOT NULL THEN
                neptuneCoreDepth(top_hole_id,sample_top) * -1.
            ELSE
                -9999.
            END AS top_depth,
        scale,
        9999 AS calibration_year,event_extent,a.event_id,
        9999 AS event_synon_to,bottom_hole_id
        FROM neptune_event a, neptune_event_def b, neptune_gpts c
        WHERE a.event_id = b.event_id
        AND b.event_id = c.event_id
        AND top_hole_id = '%s'
        AND scale = '%s'
        ORDER BY plot_fossil_group,datum_name
    """ % (holeID, toScale)
    # Use Pandas to run query and retrieve a dataframe of the sql results
    dfDATUMS = psql.read_sql_query(sqlDATUM, engine)
    # Fix depths (null)
    for i in range(0,len(dfDATUMS)):
        if (dfDATUMS['top_depth'][i] == -9999.):
            dfDATUMS['top_depth'][i] = dfDATUMS['bottom_depth'][i]
        elif (dfDATUMS['bottom_depth'][i] == -9999.):
            dfDATUMS['bottom_depth'][i] = dfDATUMS['top_depth'][i]
        dfDATUMS['datum_name'][i] = dfDATUMS['datum_name'][i].encode('utf-8')
    return dfDATUMS

def query_cores(engine,holeID): #Work
    """Query for cores from database."""
    sqlCORE = """
        SELECT core,core_top_mbsf * -1. AS top_depth,
        (core_top_mbsf + core_length) * -1. AS bottom_depth,
        core_length AS core_length
        FROM neptune_core
        WHERE hole_id = '%s'
        ORDER BY top_depth
    """ % (holeID,)
    dfCORES = psql.read_sql_query(sqlCORE,engine)
    return dfCORES

def query_paleomag_interval(engine,holeID): #Work
    """Query for paleomag intervals from database."""
    sqlPMAG = """
        SELECT top_depth * -1. AS top_depth,bottom_depth * -1. AS bottom_depth,
        color,pattern,width
        FROM neptune_hole_summary a, neptune_paleomag_interval b
        WHERE a.site_hole = b.site_hole
        AND hole_id = '%s'
    """ % (holeID,)
    dfPMAGS = psql.read_sql_query(sqlPMAG,engine)
    return dfPMAGS

# FIX_ functions:
def fix_null(t,fixType):
    """Fix missing values for depths."""
    if (pd.isnull(t)):
        t = -9999.
    elif (type(t) == str and t.strip() == ''):
        t = -9999.
    if (fixType):  # Ages (fixType = 1), return a float value
        return float(t)
    else:
        return t

def fix_cores(dfCORES):
    """Fix core depths read from file, make the depths negative"""
    for i in range(0,len(dfCORES)):
        dfCORES['top_depth'][i] = dfCORES['top_depth'][i] * -1.
        dfCORES['bottom_depth'][i] = dfCORES['bottom_depth'][i] * -1.
    return dfCORES

# CALC_ functions:
def calc_core_depth(origCore,dfCORES):
    """Calculate mbsf depth for cores (core-section,int)."""
    ccFlag = 0
    origCore = origCore.strip()
    if (origCore[0] == '-'):
        origCore = origCore[1:]
    if (origCore[0] == '?'):
        origCore = origCore[1:]
    if (origCore.find('(') > 0):
        origCore = origCore[0:origCore.find('(')-1]
    coreIdx = int(origCore[0:origCore.find('-')])-1
    topDepth = dfCORES['top_depth'][coreIdx]
    botDepth = dfCORES['bottom_depth'][coreIdx]
    section = origCore[origCore.find('-')+1:]
    if (section[0] == 'C'):  # Is this a core-catcher?
        if (section.find(',') > 0):  # CC,int
            topDepth = dfCORES['bottom_depth'][coreIdx]
            section = '1'
            ccFlag = 1
        else:
            depth = dfCORES['bottom_depth'][coreIdx]  # CC but not CC,int
            return depth
    if (ccFlag == 0):
        section = section[0:section.find(',')]
    interval = origCore[origCore.find(',')+1:]
    depth = topDepth + (int(section)-1) * 1.5 + .01 * float(interval)
    return depth

def calc_depth_ma(depth,x,y):
    """Calculate age from depth along LOC"""
    # DEV: what about event at hiatus depth?
    if (depth < abs(y[0]) or depth > abs(y[len(y)-1])): # Outside of LOC range
        return -999.
    i = 0
    while (depth >= abs(y[i])):
        i += 1
    ma = x[i-1]
    ratio = (depth - abs(y[i-1])) / (abs(y[i]) - abs(y[i-1]))
    if (ratio > 0):
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

    if (m == 0):
        n = new[0]
    elif (m == len(fromScale)):
        n = new[-1]
    else:
        n = new[m-1] + (age - old[m-1])*(new[m]-new[m-1])/(old[m]-old[m-1])
    age = n

    return(age)

def get_minmax_ages_datum(dfDATUMS):
    """Get min/max for ages (x axis) from the datums dataframe
        as a list.
    """
    ages = []
    ages.append(min(dfDATUMS['datum_age_max_ma'].tolist()))
    ages.append(max(dfDATUMS['datum_age_max_ma'].tolist()))
    ages.append(min(dfDATUMS['datum_age_min_ma'].tolist()))
    ages.append(max(dfDATUMS['datum_age_min_ma'].tolist()))

    return ages

def get_minmax_depths_datum(dfDATUMS):
    """Get min/max for depths (y axis) from the datums dataframe
        as a list.
    """
    depths = []
    depths.append(min(dfDATUMS['top_depth'].tolist()))
    depths.append(max(dfDATUMS['top_depth'].tolist()))
    depths.append(min(dfDATUMS['bottom_depth'].tolist()))
    depths.append(max(dfDATUMS['bottom_depth'].tolist()))

    return depths

def get_minmax_ages_loc(dfLOC,ages):
    """Get min/max ages from LOC and append to ages list."""
    ages.append(min(dfLOC['age_ma'].tolist()))
    ages.append(max(dfLOC['age_ma'].tolist()))
    return ages

def get_minmax_depths_loc(dfLOC,depths):
    """Get min/max depths from LOC and append to depths list."""
    depths.append(min(dfLOC['depth_mbsf'].tolist()))
    depths.append(max(dfLOC['depth_mbsf'].tolist()))

    return depths

def get_minmax_depths_cores(dfCORES,depths):
    """Get min/max depths from cores and append to depths list."""
    depths.append(min(dfCORES['top_depth'].tolist()))
    depths.append(max(dfCORES['top_depth'].tolist()))
    depths.append(min(dfCORES['bottom_depth'].tolist()))
    depths.append(max(dfCORES['bottom_depth'].tolist()))

    return depths

def get_minmax_axes(ages,depths):
    """Extract min/max for age(x) and depth(y) from lists."""
    xMinAge = min(ages)
    xMaxAge = max(ages)
    yMinDepth = min(depths)
    yMaxDepth = max(depths)

    xMin = math.floor((min(ages)/10.))*10
    xMax = math.ceil((max(ages)/10.))*10
    yMin = math.floor((min(depths)/10.))*10
    yMax = math.ceil((max(depths)/10.))*10

    # Check if user supplied axes arguments
    # and replace values for min/max axes
    # First initialize pxMin,pxMax
    pxMin = -999.
    pxMax = 999.

    if (len(sys.argv) > 8):
        pxMin = sys.argv[8]
        pxMax = sys.argv[9]
        pyMin = sys.argv[10]
        pyMax = sys.argv[11]

        xMin = float(pxMin)
        xMax = float(pxMax)
        # Now flip the y axes to negative
        yMax = float(pyMin) * -1.
        yMin = float(pyMax) * -1.

    # Check for too much padding on the x-axis
    if (xMax-xMaxAge > 5. and xMax != float(pxMax)):
        xMax = xMax - 5.

    # Place values into list and return
    axes = []
    axes.append(xMin)
    axes.append(xMax)
    axes.append(yMin)
    axes.append(yMax)

    return axes

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
    plotColorType = data['plotColorType']

    # Setup lists for using with AnnoteFinder
    xdata = []
    ydata = []
    plotCodeID = []

    # Save the processed data into lists for using later
    saveGroups = []
    saveRangeGroups = []
    saveRangeBoxes = []

    # Isotope and other symbol/color is '*'/'k'

    # Setup standard markers and color schemes for plotting of datum symbols
    stdMarkers    = [['F','^','^','x'],['N','D','D','x'],['R','d','d','x'],['D','8','8','x'],['M','s','s','x'], ['DN','p','p','x']]
    stdBWColors   = [['F','k','k'],['N','k','k'],['R','k','k'],['D','k','k'],['M','k','k'],['DN','k','k']]
    stdColors     = [['F','white','red'],['N','white','green'],['R','white','darkblue'],['D','white','#93B0CF'],['M','white','black'], ['DN','white','#A0522D']]
    stdFillColors = [['F','red','red'],['N','green','green'],['R','darkblue','darkblue'],['D','#93B0CF','#93B0CF'],['M','black','black'], ['DN','#A0522D','#A0522D']]

    # Map NSB Berlin event_type for datumType
    tops = ['ACME','DISP','LCO','TOP','T','Z']
    bases = ['BOT','REAP','FCO','EVOL','B']

    # plotColorType is passed in as argument
    if (plotColorType == 1):  # B&W plot
        stdColors = stdBWColors
    elif (plotColorType == 2):  # Color plot
        stdColors = stdColors
    elif (plotColorType == 3):  # Color w/Fills plot
        stdColors = stdFillColors
    else:
        stdColors = stdColors

    for i in range(0,len(dfDATUMS)):
        # Defaults for isotopes, etc.
        marker = '*'
        color = 'k'
        lcolor = 'k'
        fillstyle = 'full'

        # Using plot_fossil_group, not fossil_group
        #fossilGroup = dfDATUMS['fossil_group'][i][0]
        fossilGroup = dfDATUMS['plot_fossil_group'][i]

        datumType = dfDATUMS['datum_type'][i]
        if (datumType in tops):
            datumType = 'T'
        elif (datumType in bases):
            datumType = 'B'

        # Match fossilGroup with plotGroups for controls for
        # plot,label,highlight ...
        for j in range(0,len(plotGroups)):
            if (fossilGroup == plotGroups[j][0] and
              datumType == plotGroups[j][4]):
                plotGroupIdx = j

        # Match datum fossil_group to stdMarkers fossil_group
        for j in range(0,len(stdMarkers)):
            if (fossilGroup == stdMarkers[j][0]):
                if (datumType == 'T'): # Top
                    marker = stdMarkers[j][1]
                    color  = stdColors[j][1]
                    fillstyle = 'top'
                elif (datumType == 'B'): # Base
                    marker = stdMarkers[j][2]
                    color  = stdColors[j][2]
                    fillstyle = 'bottom'
                else:
                    marker = 'x' # For the fossil group, not a top, not a base
                    color  = stdColors[j][2]  # Make same color as base
                    fillstyle = 'full'
                lcolor = stdColors[j][2]  # Label color same as base
            if (plotColorType == 2): # Override fillstyle for color (non-fill)
                fillstyle = 'full'

        # Calculate average depth and average age
        avg_depth = (dfDATUMS['top_depth'][i] +
                     dfDATUMS['bottom_depth'][i]) / 2.
        avg_age = (dfDATUMS['datum_age_max_ma'][i] +
                   dfDATUMS['datum_age_min_ma'][i]) / 2.

        # Set the markersize
        if (plotGroups[plotGroupIdx][3] == 1):
            markersize = 9  # Highlight
        else:
            markersize = 7  # No highlight

        # Save data to lists for AnnoteFinder
        xdata.append(avg_age)
        ydata.append(avg_depth)
        label = dfDATUMS['plot_code'][i] + ':' + dfDATUMS['datum_name'][i]

        plotCodeID.append((dfDATUMS['plot_code'][i],dfDATUMS['datum_name'][i],
                           lcolor))

        # Plot range as box
        if ((dfDATUMS['top_depth'][i] > dfDATUMS['bottom_depth'][i]) &
           (dfDATUMS['datum_age_max_ma'][i] > dfDATUMS['datum_age_min_ma'][i])):
            xWidth = dfDATUMS['datum_age_max_ma'][i] - dfDATUMS['datum_age_min_ma'][i]
            yHeight = abs(dfDATUMS['top_depth'][i] - dfDATUMS['bottom_depth'][i])
            saveRangeBoxes.append([plotGroupIdx, fossilGroup+':'+datumType, dfDATUMS['datum_age_min_ma'][i], dfDATUMS['bottom_depth'][i], xWidth, yHeight, 'white'])

        # Annotate the datums with the plotCode
        # DEV: might fix this section to only use plotGroups ... either you
        # DEV: are plotting the symbol and the code, or else just the symbol ...
        if (plotCodes == 1):
            # DEV: testing box around label
            #plt.annotate(dfDATUMS['plot_code'][i], xy=(avg_age + 0.1, avg_depth),
            #                      size=8.,ha='left', color=lcolor, bbox=props)
            plt.annotate(dfDATUMS['plot_code'][i], xy=(avg_age + 0.1,avg_depth),
                                   size=7.,ha='left',color=lcolor)
        elif (plotGroups[plotGroupIdx][2] == 1):
            plt.annotate(dfDATUMS['plot_code'][i],xy=(avg_age+0.1,avg_depth),
                         size=7.,ha='left',color=lcolor)

        # Plot range of depth
        # DEV: make plotting range of depth an option/toggle?
        if (dfDATUMS['top_depth'][i] != dfDATUMS['bottom_depth'][i]):
            xline = []
            yline = []
            xline.append(avg_age)
            xline.append(avg_age)
            yline.append(dfDATUMS['top_depth'][i])
            yline.append(dfDATUMS['bottom_depth'][i])
            #plt.plot(xline, yline, 'k-', linewidth=0.5) # Plot later

            # Save to plot / toggle later
            saveRangeGroups.append([plotGroupIdx, fossilGroup+':'+datumType,
                                    xline, yline, lcolor])

        # Plot range of age
        # DEV: make plotting range of age an option/toggle?
        if (dfDATUMS['datum_age_max_ma'][i] != dfDATUMS['datum_age_min_ma'][i]):
            xline = []
            yline = []
            xline.append(dfDATUMS['datum_age_max_ma'][i])
            xline.append(dfDATUMS['datum_age_min_ma'][i])
            yline.append(avg_depth)
            yline.append(avg_depth)
            #plt.plot(xline, yline, 'k-', linewidth=0.5) # Plot later

            # Save to plot / toggle later
            saveRangeGroups.append([plotGroupIdx, fossilGroup+':'+datumType,
                                    xline, yline, lcolor])

        # Save group plotting data to list
        saveGroups.append([plotGroupIdx,fossilGroup,datumType,avg_age,
                           avg_depth,marker,markersize,color,fillstyle,label])

    # Add avg_age, avg_depth to dfDATUMS
    dfDATUMS['plot_age'] = xdata
    dfDATUMS['plot_depth'] = ydata

    # Turn lists into dataframe
    headers = ['plotGroupIdx','fossilGroup','datumType','avg_age','avg_depth',
               'marker','markersize','color','fillstyle','label']
    dfGROUPS = pd.DataFrame(saveGroups, columns=headers)

    # If any of the datums had a range, save to a group for line toggling
    if (len(saveRangeGroups) > 0):
        headers = ['plotGroupIdx','rangeGroup', 'xline', 'yline', 'color']
        dfRangeGROUPS = pd.DataFrame(saveRangeGroups, columns=headers)
    else:
        dfRangeGROUPS = []

    # If any of the datums had a box range, save to a group for rectangle toggling
    if (len(saveRangeBoxes) > 0):
        headers = ['plotGroupIdx','boxGroup', 'xmin', 'ymax', 'xWidth','yHeight', 'color']
        dfRangeBOXES = pd.DataFrame(saveRangeBoxes, columns=headers)
    else:
        dfRangeBOXES = []

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
       lid, = plt.plot(xd, yd, marker=pltLine['marker'][0],
                       markersize=pltLine['markersize'][0],
                       color=pltLine['color'][0],
                       fillstyle=pltLine['fillstyle'][0], lw=0,
                       label=pltLine['fossilGroup'][0]+":"+\
                       pltLine['datumType'][0],gid=gid)
       lines.append(lid)

    # Plot and save age-depth ranges to lines list
    for i in range(0,len(dfRangeGROUPS)):
       xd = dfRangeGROUPS['xline'][i]
       yd = dfRangeGROUPS['yline'][i]
       color = dfRangeGROUPS['color'][i]

       lidr = dfRangeGROUPS['rangeGroup'][i]+'.'+str(i)
       gid = str(dfRangeGROUPS['plotGroupIdx'][i])
       #lidr, = plt.plot(xd, yd, 'k', linewidth=0.5, gid=gid)
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
    leg = plt.legend(bbox_to_anchor=(1.0025,0.75), loc=2, borderaxespad=0.,
                     numpoints=1)
    leg.get_frame().set_alpha(0.4)

    lined = dict()
    for legline, origline in zip(leg.get_lines(), lines):
        legline.set_picker(5)  # 5 pts tolerance
        lined[legline] = origline

    def on_legend_pick(event):
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
            if (theLine.get_gid() == gid):
                theLine.set_visible(vis)

        # Match to range boxes, and toggle them too
        for i in range(0,len(boxesr)):
            theBox = boxesr[i]
            if (theBox.get_gid() == gid):
                theBox.set_visible(vis)

        if vis:
            #legline.set_alpha(1.0)  # Doesn't help, markers not lines...
            # Set color of legend text to black (on)
            for i in range(0,len(ltexts)):
                if (legLabel == ltexts[i].get_text()):
                    ltexts[i].set_color('black')
                    break
        else:
            #legline.set_alpha(0.1)  # Doesn't help, markers not lines...
            # Set color of legend text to red (off)
            for i in range(0,len(ltexts)):
                if (legLabel == ltexts[i].get_text()):
                    ltexts[i].set_color('red')
                    break

        fig.canvas.draw()

    # Register the callback for picking a line legend
    #canvas = ax.figure.canvas
    canvas.mpl_connect('pick_event', on_legend_pick)

    # Use AnnoteFinder to identify datums on plot
    af =  AnnoteFinder(xdata, ydata, plotCodeID)
    # Register the callback for AnnoteFinder
    #connect('button_press_event',af)
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
        if (dfCORES['top_depth'][i] >= yMin and
            dfCORES['bottom_depth'][i] <= yMax):
            cHeight = abs((dfCORES['bottom_depth'][i] - dfCORES['top_depth'][i]))
            rectangle = plt.Rectangle((xMax - cWidth, dfCORES['bottom_depth'][i]),
                                       cWidth, cHeight, fc='none')
            plt.gca().add_patch(rectangle)
            plt.annotate(dfCORES['core'][i],xy=(xMax -cWidth / 2.,
                         dfCORES['top_depth'][i] - (cHeight / 2.)), size=6.,
                         ha='center', va='center')
            # Plot the section subdivisions
            sections = int(abs((dfCORES['top_depth'][i] -
                                dfCORES['bottom_depth'][i]) / 1.5))
            for j in range(1,sections+1):
                yline=[]
                yline.append(dfCORES['top_depth'][i] - j * 1.5)
                yline.append(dfCORES['top_depth'][i] - j * 1.5)
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
        if (ageLevel[i] == 'Subepoch'):
            ageName[i] = ageName[i][ageName[i].find(' ') + 1:]
            if (ageName[i] == 'Upper'):
                ageName[i] = 'Late'
            elif (ageName[i] == 'Lower'):
                ageName[i] = 'Early'

    # Pad on y-axis
    cHeight = abs((yMax - yMin)*.025)
    yMaxPad = yMax + (abs(yMax - yMin)*.05)

    # DEV: make a function to determine position relative to axes, and use
    # DEV: for stages and chrons, and...
    for i in range(0,len(dfTIME)):
        if ((ageMinMa[i] >= xMin and ageMinMa[i] <= xMax and ageMaxMa[i] >= xMin and ageMaxMa[i] <= xMax)
            or (ageMinMa[i] < xMin and ageMaxMa[i] > xMin)
            or (ageMinMa[i] < xMax and ageMaxMa[i] > xMax)):
            if (ageLevel[i] == 'Epoch'):
                rectangle = plt.Rectangle((ageMinMa[i],yMaxPad-cHeight),ageMaxMa[i]-ageMinMa[i],cHeight,fc='none')
                plt.gca().add_patch(rectangle)
                rectangle = plt.Rectangle((ageMinMa[i],yMaxPad-(cHeight*2.)),ageMaxMa[i]-ageMinMa[i],cHeight,fc='none')
                plt.gca().add_patch(rectangle)
                if (ageMinMa[i] < xMin and ageName[i] != 'Holocene'):
                    plt.annotate(ageName[i],xy=((xMin+ageMaxMa[i])/2.,yMaxPad-(cHeight/2.)),size=9.,ha='center',va='center')
                elif (ageMaxMa[i] > xMax and ageName[i] != 'Holocene'):
                    plt.annotate(ageName[i],xy=((xMax+ageMinMa[i])/2.,yMaxPad-(cHeight/2.)),size=9.,ha='center',va='center')
                elif (ageName[i] != 'Holocene'):
                    plt.annotate(ageName[i],xy=((ageMinMa[i]+ageMaxMa[i])/2.,yMaxPad-(cHeight/2.)),size=9.,ha='center',va='center')
            elif (ageLevel[i] == 'Subepoch'):
            #elif (ageLevel[i] == 'Stage'): # DEV:  testing Stages, maybe an option?
                rectangle = plt.Rectangle((ageMinMa[i],yMaxPad-(cHeight*2.)),ageMaxMa[i]-ageMinMa[i],cHeight,fc='none')
                plt.gca().add_patch(rectangle)
                if (ageMinMa[i] < xMin):
                    plt.annotate(ageName[i],xy=((xMin+ageMaxMa[i])/2.,yMaxPad-(cHeight*1.2)),size=8.,ha='center',va='top')
                elif (ageMaxMa[i] > xMax):
                    plt.annotate(ageName[i],xy=((xMax+ageMinMa[i])/2.,yMaxPad-(cHeight*1.2)),size=8.,ha='center',va='top')
                else:
                    plt.annotate(ageName[i],xy=((ageMinMa[i]+ageMaxMa[i])/2.,yMaxPad-(cHeight*1.2)),size=8.,ha='center',va='top')

def plot_paleomag_interval(dfPMAGS,xMin,xMax,yMin,yMax):
    """Plot the pmag intervals."""
    xWidth = abs(xMax - xMin) * .0275
    topDepth = dfPMAGS['top_depth']
    bottomDepth = dfPMAGS['bottom_depth']
    intColor = dfPMAGS['color']
    for i in range(0,len(topDepth)):
        yHeight = abs(topDepth[i] - bottomDepth[i])
        if (intColor[i] == 1):
            color='black'
        else:
            color='white'
        rectangle = plt.Rectangle((xMin, bottomDepth[i]), xWidth, yHeight,
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
    cHeight = abs((yMax-yMin)*.025)
    for i in range(0,len(dfCHRONS)):
        if ((dfCHRONS['chron_age_min_ma'][i] >= xMin and dfCHRONS['chron_age_min_ma'][i] <= xMax
          and dfCHRONS['chron_age_max_ma'][i] >= xMin and dfCHRONS['chron_age_max_ma'][i] <= xMax)
          or (dfCHRONS['chron_age_min_ma'][i] <= xMin and dfCHRONS['chron_age_max_ma'][i] > xMin)
          or (dfCHRONS['chron_age_min_ma'][i] < xMax and dfCHRONS['chron_age_max_ma'][i] > xMax)):
            if (dfCHRONS['chron_polarity_dir'][i] == None or pd.isnull(dfCHRONS['chron_polarity_dir'][i])): # None/NaN/NULL
                rectangle = plt.Rectangle((dfCHRONS['chron_age_min_ma'][i],yMin-cHeight),dfCHRONS['chron_age_max_ma'][i]-dfCHRONS['chron_age_min_ma'][i],cHeight,fc='none')
                plt.gca().add_patch(rectangle)
                rectangle = plt.Rectangle((dfCHRONS['chron_age_min_ma'][i],yMin-(cHeight*2.)),dfCHRONS['chron_age_max_ma'][i]-dfCHRONS['chron_age_min_ma'][i],cHeight,fc='none')
                plt.gca().add_patch(rectangle)
                if (dfCHRONS['chron_age_min_ma'][i] < xMin):
                    plt.annotate(dfCHRONS['chron_name'][i][1:],xy=((xMin+dfCHRONS['chron_age_max_ma'][i])/2.,yMin-(cHeight/2.)),size=6.,ha='center',va='center')
                elif (dfCHRONS['chron_age_max_ma'][i] > xMax):
                    plt.annotate(dfCHRONS['chron_name'][i][1:],xy=((xMax+dfCHRONS['chron_age_min_ma'][i])/2.,yMin-(cHeight/2.)),size=6.,ha='center',va='center')
                else:
                    plt.annotate(dfCHRONS['chron_name'][i][1:],xy=((dfCHRONS['chron_age_min_ma'][i]+dfCHRONS['chron_age_max_ma'][i])/2.,yMin-(cHeight/2.)),size=6.,ha='center',va='center')
            elif (dfCHRONS['chron_polarity_dir'][i] == 'N'): # Normal polarity
                rectangle = plt.Rectangle((dfCHRONS['chron_age_min_ma'][i],yMin-(cHeight*2.)),dfCHRONS['chron_age_max_ma'][i]-dfCHRONS['chron_age_min_ma'][i],cHeight,fc='black')
                plt.gca().add_patch(rectangle)

def plot_axes_labels(data):
    """Plot the axes labels."""
    toScale = data['toScale']
    data['xAxisLabel'] = 'Age (Ma) '+ toScale
    data['yAxisLabel'] = 'Depth (mbsf)'
    plt.xlabel(data['xAxisLabel'])
    plt.ylabel(data['yAxisLabel'])

def plot_title(holeID):
    """Plot the title."""
    global title

    title = 'Age Depth Plot for ' + holeID
    plt.title(title)

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
        self.data = zip(xdata,ydata,annotes)
        if xtol is None:
            #xtol = ((max(xdata) - min(xdata))/float(len(xdata)))/2
            xtol = ((max(xdata) - min(xdata))/float(len(xdata)))/4
            if ytol is None:
                #ytol = ((max(ydata) - min(ydata))/float(len(ydata)))/2
                ytol = ((max(ydata) - min(ydata))/float(len(ydata)))/4

        self.xtol = xtol
        self.ytol = ytol
        if axis is None:
            self.axis = plt.gca()
        else:
            self.axis= axis
        self.drawnAnnotations = {}
        self.links = []

    def distance(self,x1,x2,y1,y2):
        """
        return the distance between two points
        """
        return math.hypot(x1 - x2, y1 - y2)

    def __call__(self,event):
        if event.inaxes:
          clickX = event.xdata
          clickY = event.ydata
          if self.axis is None or self.axis==event.inaxes:
            annotes = []
            for x,y,a in self.data:
                if (clickX-self.xtol < x < clickX+self.xtol and
                  clickY-self.ytol < y < clickY+self.ytol):
                    # DEV:  added button check
                    if (event.button == 1 or event.button == 2):
                        a = a[0]+":"+a[2]  # For plot_code, plot_color
                        btn = event.button
                    else:
                        a = a[0]+":"+a[1]+":"+a[2] # For plot_code, datum_name, color
                        btn = 3
                    annotes.append((self.distance(x,clickX,y,clickY),x,y,a))

            if annotes:
                #annotes.sort()
                #annote = annotes[0]
                #distance, x, y, annote = annote
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
            #t = axis.text(x+.10,y,"%s (%6.3f, %8.3f)"%(annote,x,y),size=7.,color=color)
            if (clickX <= x): # DEV: figure quadrant to post text
                xpos = x - .10
                ha = 'right'
            else:
                xpos = x + .10
                ha = 'left'
            if (clickY <= y):
                ypos = y - .10
                if (idx == 0):
                    va = 'top'
                else:
                    va = 'bottom'
            else:
                ypos = y + .10
                if (idx == 0):
                    va = 'bottom'
                else:
                    va = 'top'
            if (btn == 1):
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
        if (n == 1): # Header
            check_holeID = row[0]
            if check_holeID != data['holeID']:
                parent.messageboard.WriteText("*** Wrong holeID: " + check_holeID + " ***\n")
                parent.messageboard.WriteText("*** Skipping read strat file, will not plot ***\n")
                return df
            #timescale = row[1] # Not used but for clarification on time scale ...
            data['fromScale'] = row[2] # Global fromScale for paleomag age conversions
        if (n > 2): # Data
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
        if (df['bottom_depth'][i] == -9999.):
            df['bottom_depth'][i] = df['top_depth'][i]
        df['top_depth'][i] = fix_null(df['top_depth'][i],0)
        df['bottom_depth'][i] = fix_null(df['bottom_depth'][i],0)
        df['datum_age_min_ma'][i] = fix_null(df['datum_age_min_ma'][i],1)
        df['datum_age_max_ma'][i] = fix_null(df['datum_age_max_ma'][i],1)
        if (df['datum_age_min_ma'][i] == -9999.):
            df['datum_age_min_ma'][i] = df['datum_age_max_ma'][i]
        elif (df['datum_age_max_ma'][i] == -9999.):
            df['datum_age_max_ma'][i] = df['datum_age_min_ma'][i]
        if (df['top_depth'][i].find('-') > 0):
            if (df['top_depth'][i] == '0-0,0'):
                df['top_depth'][i] = 0.
            else:
                df['top_depth'][i] = calc_core_depth(df['top_depth'][i],data['dfCORES']) * -1.
        else:
            df['top_depth'][i] = float(df['top_depth'][i]) * -1.
        if (df['bottom_depth'][i].find('-') > 0):
            df['bottom_depth'][i] = \
                calc_core_depth(df['bottom_depth'][i],data['dfCORES']) * -1.
        else:
            df['bottom_depth'][i] = float(df['bottom_depth'][i]) * -1.
        datumType.append(df['plot_code'][i][0].upper())
    df['datum_type'] = datumType
    return df

def read_cores(parent,fileName,data):
    """Read cores file."""
    df = [ ] # Return empty if cancel on read
    parent.messageboard.WriteText('reading core data file\n')
    if (fileName == '.'):
        parent.messageboard.WriteText('no cores read\n')
        return df
    r = csv.reader(open(fileName,'rU'),delimiter='\t')
    d = []
    n = 0
    for row in r:
        n += 1
        if (n == 1): # Extract global holeID
            data['holeID'] = row[0]
        if (n > 2): # Data lines
            d.append({'core':int(row[0]), 'top_depth':float(row[1]),
                      'bottom_depth':float(row[2])})
    df = pd.DataFrame(d, columns = ['core', 'top_depth', 'bottom_depth'])
    return df

def read_paleomag_interval(parent,fileName):
    """Read PMAG intervals from file."""
    df = [ ] # Return empty if cancel on read
    parent.messageboard.WriteText('reading paleomag interval data file\n')
    if (fileName != '.'):
        r = csv.reader(open(fileName,'rU'),delimiter='\t')
        d = []
        n = 0
        for row in r:
            n += 1
            if (n == 1): # Check that the holeID is the correct one
                check_holeID = row[0]
                if (check_holeID != holeID):
                    parent.messageboard.WriteText("*** Wrong PMAG holeID: " + check_holeID + " ***\n")
                    parent.messageboard.WriteText("*** Skipping read PMAG file, will not plot ***\n")
                    return df
            if (n > 2): # Data lines
                d.append({'top_depth':float(row[0]),
                          'bottom_depth':float(row[1]), 'color':int(row[2]),
                          'pattern':row[3], 'width':float(row[4])})
        df = pd.DataFrame(d, columns = ['top_depth', 'bottom_depth',
                                        'color', 'pattern', 'width'])
        for i in range(len(df)):
            df['top_depth'][i] = df['top_depth'][i] * -1.
            df['bottom_depth'][i] = df['bottom_depth'][i] * -1.
    return df

def read_loc(parent,fileName, data):
    """ Read LOC from file.""" # To extract from file for age conversions (paleomag scale)
    df = [] # Return empty if Cancel on read
    parent.messageboard.WriteText('reading LOC data file\n')
    if (fileName != '.'): # Check for Cancel
        r = csv.reader(open(fileName,'rU'),delimiter='\t')
        d = []
        n = 0
        for row in r:
            n += 1
            if (n == 1): # Check that the holeID is the correct one
                check_holeID = row[0]
                if (check_holeID != data['holeID']):
                    parent.messageboard.WriteText("*** Wrong LOC holeID: " + check_holeID + " ***\n")
                    parent.messageboard.WriteText("*** Skipping read LOC file, will not plot ***\n")
                    return df
                #timeScale = row[1] # Time scale, e.g., Berg95
                data['fromScale'] = row[1] # Paleomag chron scale, e.g., CK95
            if (n > 2): # Data lines
                d.append({'age_ma':float(row[0]), 'depth_mbsf':float(row[1])})
        df = pd.DataFrame(d, columns = ['age_ma', 'depth_mbsf'])
        for i in range(len(df)):
            df['depth_mbsf'][i] = fix_null(df['depth_mbsf'][i],1) * -1.
    return df

#SET_ functions:

def set_axes(axes):
    """Set axes values for plot."""
    fieldNames = ["ageMin","ageMax","depthMin","depthMax"]
    new_axes = AxisDialog(axes)
    if new_axes.ShowModal()== wx.ID_OK:
        xmin = float(new_axes.xmin.GetValue())
        xmax = float(new_axes.xmax.GetValue())
        ymin = float(new_axes.ymin.GetValue())
        ymax = float(new_axes.ymax.GetValue())
        fieldValues = [xmin, xmax, ymin, ymax]
        while 1:
            if (fieldValues == None):
                fieldValues = axes
                break
            errmsg = ""
            for i in range(len(fieldNames)):
                if fieldValues[0] >= fieldValues[1]:
                    errmsg = 'ageMin should be < ageMax.\n'
                if fieldValues[2] >= fieldValues[3]:
                    errmsg = 'depthMin should be < depthMax.\n'
            if (errmsg == ""): break
            new_axes = AxisDialog(axes)
        return fieldValues
    else:
        return axes

#SAVE_ functions:
def save_loc(parent, holeID, x, y): #Rewritten
    """Write the current LOC to a file."""
    file = holeID + "_loc.txt"
    default = os.environ['NSBPATH'] + "/LOC/"
    wildcard = "Tab-separated files (*.txt)|*.txt"
    dlg = wx.FileDialog(None, 'Save your file', defaultDir =default, defaultFile=file, wildcard=wildcard, style=wx.FD_SAVE)
    if dlg.ShowModal() == wx.ID_OK:
        fileName = dlg.GetPath()
        toScale = 'Grad12' # For timescale and paleomag chron scale
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
    wildcard = "PNG files (*.png)|*.png"
    dlg = wx.FileDialog(None, 'Save your file', defaultDir=path, defaultFile=file, wildcard=wildcard, style=wx.FD_SAVE)
    if dlg.ShowModal() == wx.ID_OK:
        fileName = dlg.GetPath()
        fig.savefig(fileName)
    parent.messageboard.WriteText('saving figure to %s\n' % (fileName,))

def project_events(parent, dfDATUMS,x,y):
    """Write projected ages of events to file"""
    file = parent.holeID + "_proj.txt"
    default = os.environ['NSBPATH'] + "/PROJ/"
    wildcard = "Tab-separated files (*.txt)|*.txt"
    dlg = wx.FileDialog(None, 'Save your file', defaultDir =default, defaultFile=file, wildcard=wildcard, style=wx.FD_SAVE)
    if dlg.ShowModal() == wx.ID_OK:
        fileName = dlg.GetPath()
        # Extract a subset of column data in a new order for reporting
        dfLIST = dfDATUMS[['plot_fossil_group', 'datum_type', 'datum_name',
                           'plot_code', 'plot_depth', 'plot_age']]
        # Sort by fossil group, depth, name
        dfLIST = dfLIST.sort(['plot_fossil_group', 'plot_depth', 'datum_name'],
                              ascending=[True,False,True])
        # Re-index the new sorted dataframe
        newIndex=range(0,len(dfLIST))
        dfLIST['newIndex'] = newIndex
        dfLIST = dfLIST.set_index('newIndex')
        fo = open(fileName,"w")
        date = datetime.date.today().isoformat()
        header = []
        header.append(parent.holeID)
        header.append('v0.1')
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
            proj_age_extension = proj_age - dfLIST['plot_age'][i]
            row = []
            row.append(dfLIST['plot_fossil_group'][i])
            row.append(dfLIST['datum_type'][i])
            row.append(dfLIST['datum_name'][i])
            row.append(dfLIST['plot_code'][i])
            row.append(str(dfLIST['plot_depth'][i]))
            row.append(str(dfLIST['plot_age'][i]))
            row.append(str(round(proj_age,3)))
            row.append(str(round(proj_age_extension,3)))
            fo.write("\t".join(map(str,row))+"\n")

        fo.close()

# New GUI (JR) below:
# Wrappers:

def ADP_Menubar(parent): # Menubar
    menubar = wx.MenuBar()
    File = wx.Menu()
    File1 = File.Append(wx.ID_EXIT, '&Quit\tCtrl+Q')
    File2 = File.Append(wx.ID_ANY, 'About')
    View = wx.Menu()
    View1 = View.Append(wx.ID_ANY, 'General Help')
    View2 = View.Append(wx.ID_ANY, 'Plot Interaction Help')
    menubar.Append(File, 'File')
    menubar.Append(View, 'View')
    parent.Bind(wx.EVT_MENU, parent.Quit, File1)
    parent.Bind(wx.EVT_MENU, parent.About, File2)
    parent.Bind(wx.EVT_MENU, parent.Help, View1)
    parent.Bind(wx.EVT_MENU, parent.PIH, View2)
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
        SELECT DISTINCT leg,a.site_hole,a.hole_id AS hole_id,latitude,
        longitude,COUNT(DISTINCT(core,section_number,sect_interval_top))
        AS sample_count,water_depth,meters_penetrated,meters_recovered,
        ocean_code
        FROM neptune_hole_summary a, neptune_sample b, neptune_event_hole_index_v c
        WHERE a.hole_id = b.hole_id
        AND b.hole_id = c.hole_id
        GROUP BY 1,2,3,4,5,7,8,9,10
        UNION
        SELECT DISTINCT leg,a.site_hole,a.hole_id AS hole_id,latitude,
        longitude,0 AS sample_count,water_depth,meters_penetrated,
        meters_recovered,ocean_code
        FROM neptune_hole_summary a, neptune_event_hole_index_v c
        WHERE a.hole_id = c.hole_id
        AND c.hole_id NOT IN
        (SELECT DISTINCT a.hole_id
        FROM neptune_hole_summary a, neptune_sample b
        WHERE a.hole_id = b.hole_id)
        ORDER BY leg,site_hole
        """
        dfHOLES = psql.read_sql_query(sqlHOLES, engine)
        dfHoleList = dfHOLES[['hole_id','ocean_code','latitude','longitude','sample_count',
                        'water_depth','meters_penetrated','meters_recovered']]
        newIndex=range(0,len(dfHoleList))
        dfHoleList['newIndex'] = newIndex
        self.holeList = dfHoleList.T.to_dict().values()
        self.list_ctrl = wx.ListCtrl(self, size=(-1,450), style = wx.LC_REPORT|wx.BORDER_SUNKEN|wx.LC_SINGLE_SEL)
        self.list_ctrl.InsertColumn(0,'hole_id')
        self.list_ctrl.InsertColumn(1,'ocean_code')
        self.list_ctrl.InsertColumn(2,'latitude')
        self.list_ctrl.InsertColumn(3,'longitude')
        self.list_ctrl.InsertColumn(4,'sample_count')
        self.list_ctrl.InsertColumn(5,'water_depth')
        self.list_ctrl.InsertColumn(6,'meters_penetrated')
        self.list_ctrl.InsertColumn(7,'meters_recovered')
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(self.list_ctrl, 0, wx.ALL|wx.EXPAND, 5)
        for data in self.holeList:
            self.list_ctrl.InsertStringItem(self.index, str(data['hole_id']))
            self.list_ctrl.SetStringItem(self.index, 1, str(data['ocean_code']))
            self.list_ctrl.SetStringItem(self.index, 2, str(data['latitude']))
            self.list_ctrl.SetStringItem(self.index, 3, str(data['longitude']))
            self.list_ctrl.SetStringItem(self.index, 4, str(data['sample_count']))
            self.list_ctrl.SetStringItem(self.index, 5, str(data['water_depth']))
            self.list_ctrl.SetStringItem(self.index, 6, str(data['meters_penetrated']))
            self.list_ctrl.SetStringItem(self.index, 7, str(data['meters_recovered']))
            self.index += 1
        hor = Ok_Cancel_Wrapper(self)
        sizer.Add(hor)
        self.SetSizerAndFit(sizer)
        self.Layout()

class GetFilesDialog(wx.Dialog): # Dialog to choose files to work with
    def __init__(self, parent, data):
        wx.Dialog.__init__(self, parent, -1, 'Load relevant files', size=(400,180))
        flex = wx.FlexGridSizer(9,3,5,5)
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
        if data['plotLOC'] == 1:
            flex.Add(wx.StaticText(self, label= ' LOC File ', style=wx.ALIGN_LEFT))
            self.locfile = wx.TextCtrl(self, size=(300,-1))
            button_loc = wx.Button(self,wx.ID_ANY, label='Find LOC file')
            button_loc.Bind(wx.EVT_BUTTON, self.locLookUp)
            flex.Add(self.locfile)
            flex.Add(button_loc)
        hor = Ok_Cancel_Wrapper(self)
        flex.Add((20,20))
        flex.Add(hor)
        flex.AddGrowableCol(1)
        self.SetSizerAndFit(flex)
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
        hor = Ok_Cancel_Wrapper(self)
        flex.Add((20,20))
        flex.Add(hor)
        flex.AddGrowableCol(1)
        self.SetSizerAndFit(flex)
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
        flex.Add(wx.StaticText(self, label= ' Plot Line-of-Correlation: ', style=wx.ALIGN_LEFT))
        self.show_loc = wx.RadioBox(self, choices=['Yes','No'], majorDimension=1, style=wx.RA_SPECIFY_ROWS)
        flex.Add(self.show_loc)
        flex.Add(wx.StaticText(self, label= ' Plot Paleomag: ', style=wx.ALIGN_LEFT))
        self.show_pmag = wx.RadioBox(self, choices=['Yes','No'], majorDimension=1, style=wx.RA_SPECIFY_ROWS)
        self.show_pmag.SetSelection(1) # Defaults to No
        flex.Add(self.show_pmag)
        flex.Add(wx.StaticText(self, label= ' Set Axes Values: ', style=wx.ALIGN_LEFT))
        self.set_axes = wx.RadioBox(self, choices=['Yes','No'], majorDimension=1, style=wx.RA_SPECIFY_ROWS)
        self.set_axes.SetSelection(1) # Defaults to No
        flex.Add(self.set_axes)
        hor = Ok_Cancel_Wrapper(self)
        flex.Add((20,20))
        flex.Add(hor)
        flex.AddGrowableCol(1)
        self.SetSizerAndFit(flex)
        self.Layout()

class AxisDialog(wx.Dialog): # Dialog to set the axes
    def __init__(self,axes):
        wx.Dialog.__init__(self, None, -1, 'Enter New Axis', size=(400,180))
        flex = wx.FlexGridSizer(9,2,5,5)
        flex.Add(wx.StaticText(self, label= ' min Age ', style=wx.ALIGN_LEFT))
        self.xmin = wx.TextCtrl(self, size=(300,-1))
        self.xmin.SetValue(str(axes[0]))
        flex.Add(self.xmin)
        flex.Add(wx.StaticText(self, label= ' max Age ', style=wx.ALIGN_LEFT))
        self.xmax = wx.TextCtrl(self, size=(300,-1))
        self.xmax.SetValue(str(axes[1]))
        flex.Add(self.xmax)
        flex.Add(wx.StaticText(self, label= ' min Depth ', style=wx.ALIGN_LEFT))
        self.ymin = wx.TextCtrl(self, size=(300,-1))
        self.ymin.SetValue(str(axes[2]))
        flex.Add(self.ymin)
        flex.Add(wx.StaticText(self, label= ' max Depth ', style=wx.ALIGN_LEFT))
        self.ymax = wx.TextCtrl(self, size=(300,-1))
        self.ymax.SetValue(str(axes[3]))
        flex.Add(self.ymax)
        hor = Ok_Cancel_Wrapper(self)
        flex.Add((20,20))
        flex.Add(hor)
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
        hor = Ok_Cancel_Wrapper(self)
        flex.Add((20,20))
        flex.Add(hor)
        flex.AddGrowableCol(1)
        self.SetSizerAndFit(flex)
        self.Layout()

# Help/Info frames:
class AboutFrame(wx.Frame):
    def __init__(self, parent):
        wx.Frame.__init__(self, parent, size=(800,500))
        html = wx.html.HtmlWindow(self)
        fileName = os.environ['NSBPATH'] + "/REF/program_about.txt"
        html.LoadFile(fileName)
        self.Show()

class PIHFrame(wx.Frame):
    def __init__(self, parent):
        wx.Frame.__init__(self, parent, size=(800,500))
        html = wx.html.HtmlWindow(self)
        fileName = os.environ['NSBPATH'] + "/REF/plot_help.txt"
        html.LoadFile(fileName)
        self.Show()

class HelpFrame(wx.Frame):
    def __init__(self, parent):
        wx.Frame.__init__(self, parent, size=(800,500))
        html = wx.html.HtmlWindow(self)
        fileName = os.environ['NSBPATH'] + "/REF/program_help.txt"
        html.LoadFile(fileName)
        self.Show()

class ListEventsFrame(wx.Frame):
    def __init__(self, parent, data):
        wx.Frame.__init__(self, parent, size=(750,500), title="List Events",pos=(300,50))
        #wx.Dialog.__init__(self, parent, -1, title="NSB-ADP: List Events",size=(750,500), pos=(300,10))
        dfLIST = data['dfDATUMS'][['plot_fossil_group', 'datum_type', 'datum_name',
                          'plot_code', 'datum_age_min_ma', 'datum_age_max_ma',
                          'top_depth','bottom_depth', 'plot_age', 'plot_depth']]
        dfLIST = dfLIST.sort(['plot_fossil_group','top_depth','datum_name'], ascending=[True,False,True])
        self.index = 0
        self.eventList = dfLIST.T.to_dict().values()
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
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(self.list_ctrl, 0, wx.ALL|wx.EXPAND, 5)
        for data in self.eventList:
            self.list_ctrl.InsertStringItem(self.index, str(data['plot_fossil_group']))
            self.list_ctrl.SetStringItem(self.index, 1, str(data['datum_type']))
            self.list_ctrl.SetStringItem(self.index, 2, str(data['datum_name']))
            self.list_ctrl.SetStringItem(self.index, 3, str(data['plot_code']))
            self.list_ctrl.SetStringItem(self.index, 4, str(data['datum_age_min_ma']))
            self.list_ctrl.SetStringItem(self.index, 5, str(data['datum_age_max_ma']))
            self.list_ctrl.SetStringItem(self.index, 6, str(data['top_depth']))
            self.list_ctrl.SetStringItem(self.index, 7, str(data['bottom_depth']))
            self.list_ctrl.SetStringItem(self.index, 8, str(data['plot_age']))
            self.list_ctrl.SetStringItem(self.index, 9, str(data['plot_depth']))
            self.index += 1
        self.SetSizer(sizer)
        self.Show(True)
        #self.Layout()

class LOCFrame(wx.Frame):
    def __init__(self, parent, x,y):
        wx.Frame.__init__(self, parent, size=(200,400), title="Inspect LOC",pos=(300,50))
        self.index = 0
        self.list_ctrl = wx.ListCtrl(self, size=(-1,400), style = wx.LC_REPORT|wx.BORDER_SUNKEN|wx.LC_SINGLE_SEL)
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
        wx.Frame.__init__(self, None, -1, 'Age-Depth Plot', size=(500, 300))
        self.messageboard = parent.messageboard
        data['plotGroups'] = get_plot_groups(data['dfDATUMS'],data['plotCodes'])
        # Setup axes
        axes = self.process_axes(data)
        # Plot
        self.fig = plt.figure()
        self.messageboard.WriteText('plotting...\n')
        self.canvas = FigureCanvas(self, -1, self.fig)
        self.plot(data, axes)
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
        self.toolbar = NavigationToolbar2Wx(self.canvas)
        self.toolbar.Realize()
        self.sizer.Add(self.toolbar, 0, wx.LEFT | wx.EXPAND)
        self.toolbar.update()
        # Setup menubar
        self.menubar = ADP_Menubar(self)
        Save = wx.Menu()
        Save1 = Save.Append(wx.ID_ANY, 'Save Plot')
        Save2 = Save.Append(wx.ID_ANY, 'Save LOC')
        Save3 = Save.Append(wx.ID_ANY, 'Inspect LOC')
        Save4 = Save.Append(wx.ID_ANY, 'Inspect Stratigraphic data')
        Save5 = Save.Append(wx.ID_ANY, 'Project events on LOC')
        self.menubar.Append(Save, 'Plot')
        self.Bind(wx.EVT_MENU, lambda event: save_plot(self, self.holeID, self.fig), Save1)
        self.Bind(wx.EVT_MENU, lambda event: save_loc(self, self.holeID, self.line), Save2)
        self.Bind(wx.EVT_MENU, lambda event: self.inspect_loc(self.line.get_data()[0], self.line.get_data()[1]), Save3)
        self.Bind(wx.EVT_MENU, lambda event: self.list_events(data), Save4)
        self.Bind(wx.EVT_MENU, lambda event: project_events(self,data['dfDATUMS'],self.line.get_data()[0], self.line.get_data()[1]), Save5)
        self.SetMenuBar(self.menubar)
        self.Show(True)

    def plot(self,data,axes):
        self.ax = self.fig.add_subplot(111)
        self.xMin = max(axes[0],0)
        self.xMax = axes[1]
        self.yMin = axes[2]
        self.yMax = axes[3]
        self.ax.set_xlim([self.xMin,self.xMax])
        self.ax.set_ylim([self.yMin - (abs(self.yMax - self.yMin) * 0.05), self.yMax + (abs(self.yMax - self.yMin) * .05)])
        #Plotting
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
        plot_axes_labels(data)
        plot_title(data['holeID'])
        #Prepare LOC
        locList = []
        locData = []
        if len(data['dfLOC']) == 0:
            locData = [(self.xMin,self.yMax),(self.xMax,self.yMin)]
        else:
            for i in range(0,len(data['dfLOC'])):
                locData.append((data['dfLOC']['age_ma'][i], data['dfLOC']['depth_mbsf'][i]))
        locList.append(list(locData))
        locIdx = 0
        # Instantiate many variables
        self.showverts = True
        self.showHiatus = True
        self.epsilon = 5
        self.locList = locList
        self.locIdx = locIdx
        toScale = data['toScale']
        self.dfDATUMS = data['dfDATUMS']
        self.plotGroups = data['plotGroups']
        self.plotCodes = data['plotCodes']
        self.plotColorType = data['plotColorType']
        self.holeID = data['holeID']
        # Initialize for use later
        self.color = 'g'
        self.linestyle = '-'
        self.linewidth = 1
        self.hcolor = 'r'
        self.hlinestyle = ':'
        self.hlinewidth = 2.5
        self.hLines = []
        self.locIdx = locIdx
        # For 'e' - Edit Labels
        self.title = title
        self.xAxisLabel = data['xAxisLabel']
        self.yAxisLabel = data['yAxisLabel']
        if (self.plotColorType == 1):
            self.color = 'k'
            self.linestyle = '--'
        else:
            self.color = 'g'
            self.linestyle = '-'
        # Plot line of correlation
        x, y = zip(*self.locList[self.locIdx])
        self.line, = self.ax.plot(x, y, marker='s', markerfacecolor=self.color, color=self.color,
                                  linestyle=self.linestyle, linewidth=self.linewidth, markersize=3, animated=False)
        # Plot hiatuses
        self.plot_hiatuses()
        # Setup index for pick of a vertex
        self._ind = None

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

        if (event.key == 'i'):  # Insert
            return ind

        if (event.key == 'd'):  # Delete
            if (d[ind] >= self.epsilon):  # Check within epsilon distance
                ind = None
            return ind

        if (event.button):  # DEV: make a point was selected
            if (d[ind] > self.epsilon):
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

        self.new_loc(x, y) # add a new LOC to locList

        self.ax.lines.remove(self.line) # remove the line currently plotting
        x, y = zip(*self.locList[self.locIdx]) # create a new line with inserted point

        self.line, = self.ax.plot(x, y, marker='s', markerfacecolor=self.color, color=self.color,
                                  linestyle=self.linestyle, linewidth=self.linewidth, markersize=3, animated=False)

        # Plot hiatuses
        self.plot_hiatuses()

    def key_press_callback(self, event):
        """Whenever a key is pressed."""
        if not event.inaxes:
            return

        if (event.key == 't'): # Toggle visibility of the line
            self.showverts = not self.showverts
            self.line.set_visible(self.showverts)
            if not self.showverts: self._ind = None
            self.showHiatus = not self.showHiatus # Toggle hiatuses
            for i in range (0,len(self.hLines)):
                aLine = self.hLines[i]
                setp(aLine, visible=self.showHiatus)
            self.canvas.draw()

        elif (event.key =='i'): # Insert a vertex to the line
            is_valid = 0 # reset every time ...
            ind = self.get_ind_under_point(event)
            x, y = self.line.get_data()
            if (not type(x) is list): # First time convert np.array to list
                x = x.tolist()
                y = y.tolist()
            if (event.xdata > x[ind]): # Check to adjust ind for insert position
                ind = ind + 1
            # Determine if valid position and insert or append vertex
            if (event.xdata > x[len(x)-1] and event.ydata <= y[len(y)-1]):
                # Append after last point
                x.append(event.xdata)
                y.append(event.ydata)
                is_valid = 1
            elif (event.xdata < x[0] and event.ydata >= y[0]):
                # Insert before first point
                x.insert(0, event.xdata)
                y.insert(0, event.ydata)
                is_valid = 1
            elif (ind <= (len(x)-1) and
                  event.xdata < x[ind] and event.ydata >= y[ind] and
                  event.xdata > x[ind-1] and event.ydata < y[ind-1]):
                # Insert point
                x.insert(ind, event.xdata)
                y.insert(ind, event.ydata)
                is_valid = 1

            # DEV:  don't set the line, you are going to remove and plot the new one ...
            #self.line.set_data(x, y)

            if (is_valid): # was it a valid insert?
                self.new_loc(x, y) # add a new LOC to locList

                self.ax.lines.remove(self.line) # remove the line currently plotting
                x, y = zip(*self.locList[self.locIdx]) # create a new line with inserted point

                self.line, = self.ax.plot(x, y, marker='s', markerfacecolor=self.color, color=self.color,
                                  linestyle=self.linestyle, linewidth=self.linewidth, markersize=3, animated=False)

                # Plot hiatuses
                self.plot_hiatuses()
                self.canvas.draw()

        elif (event.key == 'd'): # Delete a vertex of the line
            ind = self.get_ind_under_point(event)
            if (ind is not None):
                x, y = self.line.get_data()
                if (not type(x) is list):
                    x = x.tolist()
                    y = y.tolist()
                # Remove x and y from list at ind
                x.pop(ind)
                y.pop(ind)
                #self.line.set_data(x, y)

                self.new_loc(x, y) # add a new LOC to locList

                self.ax.lines.remove(self.line) # remove the line currently plotting
                x, y = zip(*self.locList[self.locIdx]) # create a new line with inserted point

                self.line, = self.ax.plot(x, y, marker='s', markerfacecolor=self.color, color=self.color,
                                          linestyle=self.linestyle, linewidth=self.linewidth, markersize=3, animated=False)

                # Plot hiatuses
                self.plot_hiatuses()
                self.canvas.draw()

        elif (event.key == 's'): # Save LOC to file
            x, y = self.line.get_data()
            save_loc(self, self.holeID, x, y)

        elif (event.key == 'I'): # Inspect LOC
            x, y = self.line.get_data()
            self.inspect_loc(x, y)

        elif (event.key == 'p'): # Save plot to file
            save_plot(self, self.holeID, self.fig)

        elif (event.key == 'l'):  # List events
            #ListEventsFrame(None,data)
            self.list_events(data)

        elif (event.key == 'c'): # Project events
            x, y = self.line.get_data()
            project_events(self,data['dfDATUMS'], x, y)

        elif (event.key == 'a'): # Set axes
            axes = [self.xMin,self.xMax,self.yMin,self.yMax]
            newAxes = set_axes(axes)
            self.xMin = float(newAxes[0])
            self.xMax = float(newAxes[1])
            self.yMin = float(newAxes[2])
            self.yMax = float(newAxes[3])
            self.messageboard.WriteText('new axis:\nxMin=%.2f, xMax=%.2f, yMin=%.2f, yMax=%.2f\n' % (self.xMin, self.xMax, self.yMin, self.yMax))
            self.ax.axis(newAxes)
            self.set_plot_limits(self.xMin,self.xMax,self.yMin,self.yMax)
            plt.clf()
            self.plot(data,newAxes)
            self.canvas.draw()

        elif (event.key == 'e'): # Edit title and/or axes labels
            labels = [self.title,self.xAxisLabel,self.yAxisLabel]
            labels = set_labels(labels)
            self.title = labels[0]
            self.xAxisLabel = labels[1]
            self.yAxisLabel = labels[2]
            plt.title(self.title)
            plt.xlabel(self.xAxisLabel)
            plt.ylabel(self.yAxisLabel)
            self.canvas.draw()

        elif (event.key == 'h'): # Plot Help
            self.PIH()

        elif (event.key == 'H'): # Program Help
            self.Help()

        elif (event.key == 'x'): # Exit
            self.Quit(event)

    def motion_notify_callback(self,event):
        '''on mouse movement'''
        if event.inaxes: self.statusBar.SetStatusText(("x= %.3f y=%.2f"%(event.xdata,event.ydata)), 0)
        if not self.showverts: return
        if self._ind is None: return
        if event.inaxes is None: return
        if event.button != 1: return
        x,y = self.line.get_data()
        if (not type(x) is list):
            x = x.tolist()
            y = y.tolist()

        # DEV: determine boundaries for moving a point
        # DEV: first point, make xBounds to x axis min, y axis max
        # DEV: modified code from Neptune ADP (Java)...
        if (self._ind == 0):
            xBound0 = self.xMin
            yBound0 = self.yMax
        else:
            # Previous point
            xBound0 = x[self._ind - 1]
            yBound0 = y[self._ind - 1]

        if (self._ind == len(x) - 1): # Last point
            xBound1 = self.xMax
            yBound1 = self.yMin
        else:
            xBound1 = x[self._ind + 1] # Next point
            yBound1 = y[self._ind + 1]

        # Don't exceed x boundaries
        if (event.xdata < xBound0):
            event.xdata = xBound0
        elif (event.xdata > xBound1):
            event.xdata = xBound1

        # Don't exceed y boundaries
        if (event.ydata > yBound0):
            event.ydata = yBound0
        elif (event.ydata < yBound1):
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
        if (not type(x) is list): # First time convert np.array to list
            x = x.tolist()
            y = y.tolist()

        # Check for hiatuses and plot
        for i in range (0,len(x)-1): # Check x(age) at different y(depth)
            #if ((abs(y[i+1])-abs(y[i]) == 0.) or (abs(y[i+1])-abs(y[i]))/(x[i+1]-x[i]) <= 1.): # <=1meter/ma accumulation
            if ((abs(y[i+1])-abs(y[i]) == 0.) or (abs(y[i+1])-abs(y[i]))/(x[i+1]-x[i]) <= 0.5): # <=0.5meter/ma accumulation
                xh = [x[i], x[i+1]]
                yh = [y[i], y[i+1]]

            #
            #DEV:  need to fix this
            #if ((abs(y[i+1])-abs(y[i]) == 0.) or (abs(y[i+1])-abs(y[i]))/(x[i+1]-x[i]) <= 0.5): # <=0.5meter/ma accumulation
            #    ZeroDivisionError: float division by zero
            #

                self.hlinewidth = 2.5

                if (self.plotColorType == 1): # Black & White plot
                    self.hcolor = 'k'
                    self.hlinestyle = ':'
                else: # Color plot
                    self.hcolor = 'r'
                    self.hlinestyle = ':'
                if (y[i] != y[i+1]): # Almost a hiatus - alert user

                    # DEV:  if you are this close, make the depth values the same (snap) ...
                    # DEV:  depends on which point ...
                    #yh = [y[i], y[i]] # setting point on older age to depth of younger age
                    #yh = y[i+i], y[i+i] # setting point on younger age to depth of older age

                    # DEV:  need to go back and make the y[i+1] = y[i] OR y[i] = y[i+1]
                    # DEV:  depends on which point was moved ...
                    # DEV:  for now, make the line BIG to alert the user
                    self.messageboard.WriteText('alert - to make a hiatus adjust point to same depth\n')
                    self.hlinestyle = '-.'
                    self.hlinewidth = 12.

                # Plot and save line to list
                self.hLines.append(self.ax.plot(xh, yh, marker='s',
                                   markerfacecolor=self.hcolor, color=self.hcolor,
                                   linestyle=self.hlinestyle, linewidth=self.hlinewidth))

    def new_loc(self,x, y): #Rewritten
        """Adding a LOC to list of LOC's."""
        newLoc =[]
        for i in range(0,len(x)):
            newLoc.append((x[i], y[i]))
        self.locList.append(list(newLoc))
        self.locIdx += 1

    def crop_loc(idx): #Rewritten
        """Crop list of LOC's to current one."""
        self.locList = self.locList[0:idx]
        set_locIdx(len(self.locList)-1)

    def del_loc(idx): #Rewritten
        """Delete a LOC from list of LOC's."""
        #locList = locList[0:idx]
        self.locList.pop(idx)
        set_locIdx(idx-1)

    def set_locIdx(idx): #Rewritten
        """Set the value of locIdx."""
        self.locIdx = idx

    def set_plot_limits(self,xMin,xMax,yMin,yMax): #Rewritten
        """Set axes limits for figure."""
        plt.xlim(xMin,xMax)
        plt.ylim(yMin - (abs(yMax - yMin) * 0.05), yMax + (abs(yMax - yMin) * .05))

    def list_events(self,data): #Rewritten
        w = ListEventsFrame(None, data)

    def inspect_loc(self,x,y): #Rewritten
        w = LOCFrame(None, x, y)

    def Quit(self,event):
        self.messageboard.WriteText('closing plot\n')
        self.Close()

    def Help(self,event):
        help = HelpFrame(None)

    def About(self,event):
        help = AboutFrame(None)

    def PIH(self,event):
        help = PIHFrame(None)

    def process_axes(self, data): # Process data to configure axes. Mostly untouched from Pat's code
        dfDATUMS = data['dfDATUMS']
        dfCORES = data['dfCORES']
        dfLOC = data['dfLOC']
        setAxes = data['setAxes']
        ages   = get_minmax_ages_datum(dfDATUMS)
        depths = get_minmax_depths_datum(dfDATUMS)
        if (len(dfLOC) != 0):
            ages  = get_minmax_ages_loc(dfLOC,ages)
            depths = get_minmax_depths_loc(dfLOC,depths)
        if (len(dfCORES) != 0):
            depths = get_minmax_depths_cores(dfCORES,depths)
        axes = get_minmax_axes(ages,depths)
        xMin = axes[0]
        xMax = axes[1]
        yMin = axes[2]
        yMax = axes[3]
        self.messageboard.WriteText('calculated axis:\nxMin=%.2f, xMax=%.2f, yMin=%.2f, yMax=%.2f\n' % (xMin, xMax, yMin, yMax))
        if (setAxes == 1):
            axes = [xMin,xMax,yMin,yMax] # ints, and positive
            newAxes = set_axes(axes)
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
        choices = ["Run Program", "General Help", "Plot Interaction Help", "About", "Exit"]
        self.action= wx.ComboBox(self, size=(-1,-1), choices=choices, style=wx.CB_READONLY|wx.CB_DROPDOWN)
        sizer.Add(wx.StaticText(self, label="Select an action"),1,wx.CENTER)
        sizer.Add(self.action,1,wx.CENTER)
        okButton = wx.Button(self, wx.ID_OK, "OK")
        okButton.Bind(wx.EVT_BUTTON, self.Start)
        sizer.Add(okButton,1,wx.CENTER)
        self.messageboard = wx.TextCtrl(self,size=(400,400),value="",style=wx.TE_READONLY|wx.TE_MULTILINE|wx.HSCROLL)
        sizer.Add(self.messageboard, 1, wx.CENTER) # Message to user will be displayed on messageboard
        outer = wx.BoxSizer(wx.HORIZONTAL)
        outer.Add(sizer,1,wx.Center)
        self.SetSizer(outer)
        self.Show(True)

    def Quit(self,event):
        self.Close()

    def Help(self,event):
        help = HelpFrame(None)

    def About(self,event):
        help = AboutFrame(None)

    def PIH(self,event):
        help = PIHFrame(None)

    def Start(self, event):
        action = self.action.GetValue() # Select action
        if action == "Run Program": self.Run()
        elif action == "General Help": self.Help(event)
        elif action == "Plot Interaction Help": self.PIH(event)
        elif action == "About": self.About(event)
        elif action == "Exit": self.Quit(event)

    def Run(self):
        params = ParamDialog(self) #Open Parameter dialog window
        data['toScale'] = "Grad12" # Default scale
        data['dfTIME'] = read_time_scale(self,data['toScale'])
        data['dfCHRONS'] = read_paleomag_scale(self,data['toScale'])
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
            data['plotLOC'] = 1 if params.show_loc.GetStringSelection()=="Yes" else 0
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
                        pass
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
            else: # If data taken from files
                files = GetFilesDialog(self, data= data) # Open the file selection dialog window
                if files.ShowModal() == wx.ID_OK: # When OK clicked, read those files accordingly
                    data['dfCORES'] = read_cores(self,files.corefile.GetValue(), data)
                    data['dfDATUMS'] = read_datums(self,files.stratfile.GetValue(), data)
                    data['dfCORES'] = fix_cores(data['dfCORES'])
                    if data['plotPMAG'] == 1: data['dfPMAGS'] = read_paleomag_interval(self,files.pmagfile.GetValue())
                    if data['plotLOC'] == 1: data['dfLOC'] = read_loc(self,files.locfile.GetValue(), data)
            self.holeID = data['holeID']
            self.messageboard.WriteText('\nHole: %s\n' % data['holeID']) # Summarize data to be plotted
            self.messageboard.WriteText('Number of events: %s\n' % len(data['dfDATUMS']))
            if 'dfLOC' in data.keys(): self.messageboard.WriteText('Number of tiepoints: %s\n\n' % len(data['dfLOC']))
            w = ADPFrame(self,data) # Go on and plot

if __name__ == '__main__':
    #Change default of matplotlib and pandas:
    matplotlib.rcParams['figure.figsize'] = 11,8
    matplotlib.rcParams['legend.numpoints'] = 2
    matplotlib.rcParams['legend.fontsize'] = 'small'
    matplotlib.rcParams['savefig.dpi'] = 400
    matplotlib.rcParams['keymap.save'] = ''
    matplotlib.rcParams['keymap.xscale'] = ''
    matplotlib.rcParams['keymap.yscale'] = ''
    matplotlib.rcParams['keymap.zoom'] = ''
    matplotlib.rcParams['keymap.pan'] = ''
    matplotlib.rcParams['keymap.home'] = ''
    pd.options.mode.chained_assignment = None
    # Find appropriate path to folders:
    if getattr(sys, 'frozen', False):
        if re.search('/Contents/',sys.executable):
            os.environ['NSBPATH'] = os.path.dirname(re.sub('/Contents/.+','',sys.executable))
        else:
            os.environ['NSBPATH'] = os.path.dirname(sys.executable)
    else:
        os.environ['NSBPATH'] = os.path.dirname(os.path.realpath(__file__))
    data = {} # This dictionary will contain every single 'global' variable and pass them around frames, dialogs, functions, etc.
    adp = wx.App(False) # Instantiate software
    frame = WelcomeFrame(None, data) # Open main frame
    adp.MainLoop() # Loop
