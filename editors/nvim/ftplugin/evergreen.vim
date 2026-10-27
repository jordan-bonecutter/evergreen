if exists('b:did_ftplugin')
  finish
endif
let b:did_ftplugin = 1

setlocal commentstring=//\ %s
setlocal comments=://
setlocal expandtab shiftwidth=4 softtabstop=4
setlocal cindent cinoptions=L0,(0,Ws,J1
setlocal suffixesadd=.evg

let b:undo_ftplugin = 'setlocal commentstring< comments< expandtab< shiftwidth< softtabstop< cindent< cinoptions< suffixesadd<'
