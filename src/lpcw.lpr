program lpcw;

{$mode delphi}{$H+}{$J-}
{$warn 5023 off}

uses
 {$IFDEF UNIX}
 {$IFDEF UseCThreads}
  cthreads,
 {$ENDIF}
 {$ENDIF}
  JMem,
  Interfaces, // this includes the LCL widgetset
  Forms,
  Main,
  ast,
  cntx,
  cupersist,
  err,
  fileutils,
  func,
  hashtable,
  lex,
  parser,
  inst,
  llvm_codegen,
  llvm_codepack,
  dump;

{$R *.res}

begin
  RequireDerivedFormResource := True;
  Application.Scaled:=True;
  Application.Initialize;
  Application.CreateForm(TMainFrm, MainFrm);
  Application.Run;
end.
