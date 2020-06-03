program lpc;

{$mode delphi}{$H+}{$J-}

uses
 {$IFDEF UNIX}
 {$IFDEF UseCThreads}
  cthreads,
 {$ENDIF}
 {$ENDIF}
  Classes,
  SysUtils,
  ast,
  ptrhashtable,
  cntx,
  cupersist,
  err,
  lex,
  parser,
  start,
  fileutils,
  func,
  hashtable,
  dump,
  llvm_codegen,
  llvm_codepack;

begin
  StartCompile;
end.
