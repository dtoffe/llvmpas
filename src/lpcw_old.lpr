program lpcw;

{$mode objfpc}{$H+}
{$warn 5023 off}

uses
  {$IFDEF UNIX}{$IFDEF UseCThreads}
  cthreads,
  {$ENDIF}{$ENDIF}
  Interfaces, // this includes the LCL widgetset
  Forms, Main, ast, cntx, cupersist, err, fileutils,
  func, hashtable, lex, parser, inst, llvm_codegen, llvm_codepack, dump;

{$R *.res}

begin
  RequireDerivedFormResource := True;
  Application.Initialize;
  Application.CreateForm(TMainFrm, MainFrm);
  Application.Run;
end.

