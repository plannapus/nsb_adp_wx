# -*- mode: python -*-

block_cipher = None

a = Analysis(['nsb_adp_wx.py'],
             pathex=[],
             binaries=None,
             datas=None,
             hiddenimports=[],
             hookspath=[],
             runtime_hooks=[],
             excludes=[],
             win_no_prefer_redirects=False,
             win_private_assemblies=False,
             cipher=block_cipher)

pyz = PYZ(a.pure, a.zipped_data,
             cipher=block_cipher)

exe = EXE(pyz,
          a.scripts,
          exclude_binaries=True,
          name='NSB_ADP',
          debug=False,
          strip=False,
          upx=True,
          console=False )

coll = COLLECT(exe, a.binaries, a.zipfiles, a.datas, strip=False, upx=True, name='NSB_ADP_wx')

app = BUNDLE(coll,
             name='NSB_ADP_wx.app',
             info_plist={'CFBundleIdentifier':'org.plannapus.nsbadp',
                                'CFBundleShortVersionString':'0.2',
                                'NSHumanReadableCopyright':'None'})
