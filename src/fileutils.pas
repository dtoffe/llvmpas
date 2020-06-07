unit fileutils;

{$ifdef FPC}
{$mode delphi}
{$H+}{$J-}
{$endif}

interface

uses SysUtils, ast;

procedure GetFileTimeStamp(const S: string; out TimeStamp: TFileTimeStamp); overload;
// procedure GetFileTimeStamp(Handle: THandle; out TimeStamp: TFileTimeStamp); overload;

implementation

{$warnings off}
{$hints off}

procedure ToTimeStamp(const T: TSystemTime; out TimeStamp: TFileTimeStamp);
begin
  TimeStamp.Date := T.Year * 10000 + T.Month * 100 + T.Day;
  TimeStamp.Time := T.Hour * 10000000 + T.Minute * 100000 + T.Second * 1000 + T.Millisecond;
end;

procedure GetFileTimeStamp(const S: string; out TimeStamp: TFileTimeStamp);
var
  fileok : Boolean;
  datetime : TDateTime;
  systime : TSystemTime;
  filedata : TSearchRec;
begin
  fileok := FindFirst(S, faAnyFile, filedata) = 0;
  if fileok then
  begin
    datetime := FileDateToDateTime(filedata.Time);
    DateTimeToSystemTime(datetime, systime);
    ToTimeStamp(systime, TimeStamp);
    FindClose(filedata);
  end;
end;

(* *** Previous version, Windows only. Delete after cross platform implemented.

procedure GetFileTimeStamp(const S: string; out TimeStamp: TFileTimeStamp);
var
  FindData: TWin32FindData;
  hFind: THandle;
  localT: TFileTime;
  sysT: TSystemTime;
begin
  TimeStamp.Date := 0;
  TimeStamp.Time := 0;
  hFind := FindFirstFile(PChar(S), FindData);
  if hFind <> INVALID_HANDLE_VALUE then
  begin
    if FileTimeToLocalFileTime(FindData.ftLastWriteTime, localT) and FileTimeToSystemTime(localT, sysT) then
    begin
      ToTimeStamp(sysT, TimeStamp);
    end;
    FindClose(hFind);
  end;
end;

procedure GetFileTimeStamp(Handle: THandle; out TimeStamp: TFileTimeStamp);
var
  lastWrite, localT: TFileTime;
  sysT: TSystemTime;
begin
  TimeStamp.Date := 0;
  TimeStamp.Time := 0;
  if GetFileTime(Handle, nil, nil, @lastWrite) and FileTimeToLocalFileTime(lastWrite, localT) and
    FileTimeToSystemTime(localT, sysT) then
  begin
    ToTimeStamp(sysT, TimeStamp);
  end;
end;
*)

end.
