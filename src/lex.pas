unit lex;

{$ifdef FPC}
{$mode delphi}
{$H+}{$J-}
{$endif}

interface

uses SysUtils, Classes, ast;

const
  SErrInvalidCharacter = 'Invalid character ''%s''';
  SErrOpenString = 'string exceeds end of line';
  SErrInvalidSwitchList = 'Invalid switch list';
  SErrInvalidOctalConst = 'Invalid octal number';
  SErrInvalidRealConst = 'Invalid real number';
  SErrInvalidIntConst = 'Invalid integer number';
  SErrIntTooLarge = 'Integer constant too large';
  SErrInvalidCharConst = 'Invalid character constant';
  SErrInvalidHexConst = 'Invalid hex number';
  SErrInvalidBinConst = 'Invalid binary number';
  SErrIncludeFileNotFound = 'Could not find include file ''%s''';
  SErrUnexpectedEOFInComment = 'Unexpected end of file in comment';
  SErrInvalidDirective = 'Invalid compiler directive: %s';
  SErrInvalidDirectiveParam = 'Invalid compiler directive parameter';
  SErrTooManyNestedCondDir = 'Too many nested conditional directives';
  SErrUntermCondDir = 'Unterminated conditional directive';
  SErrFileNotFound = 'File not found: %s';
  SErrFileOpenFailed = 'File open fail: %s';

type
  TToken = (tkEOF, tkWhitespace, tkIllegalChar, tkComment, tkDirective, tkDirectiveEnd,
    tkIdentifier, tkStrConst, tkCharConst, tkIntConst, tkHexConst, tkBinConst, tkOctalConst,
    tkFloatConst, tkBraceOpen, tkBraceClose, tkMul, tkPlus, tkComma, tkMinus, tkDot, tkFDiv,
    tkColon, tkSemicolon, tkLessThan, tkEqual, tkGreaterThan, tkAt, tkSquaredBraceOpen,
    tkSquaredBraceClose, tkCaret, tkBackslash, tkDotDot, tkAssign, tkNotEqual, tkLessEqualThan,
    tkGreaterEqualThan, tkPower, tkSymmetricalDifference, tkAbsolute, tkAbstract, tkAlias, tkAnd,
    tkArray, tkAs, tkAsm, tkAssembler, tkBegin, tkBitpacked, tkCase, tkCdecl, tkClass, tkConst,
    tkConstructor, tkDefault, tkDeprecated, tkDestructor, tkDispId, tkDispInterface, tkDiv, tkDo,
    tkDownto, tkDynamic, tkElse, tkEnd, tkExcept, tkExperimental, tkExport, tkExports, tkExternal,
    tkFalse, tkFar, tkFile, tkFinalization, tkFinally, tkFor, tkForward, tkFunction, tkGoto, tkIf,
    tkImplementation, tkIn, tkIndex, tkInherited, tkInitialization, tkInline, tkInterface, tkIs,
    tkLabel, tkLibrary, tkLocal, tkMessage, tkMod, tkNear, tkNil, tkNodefault, tkNot, tkObject,
    tkOf, tkOn, tkOperator, tkOr, tkOut, tkOverload, tkOverride, tkPacked, tkPascal, tkPlatform,
    tkPrivate, tkProcedure, tkProgram, tkProperty, tkProtected, tkPublic, tkPublished, tkRaise,
    tkRead, tkReadOnly, tkRecord, tkRegister, tkReintroduce, tkRepeat, tkResourceString, tkSafecall,
    tkSet, tkShl, tkShr, tkStatic, tkStdcall, tkStored, tkStrict, tkString, tkThen, tkThreadvar,
    tkTo, tkTrue, tkTry, tkType, tkUnimplemented, tkUnit, tkUntil, tkUses, tkVar, tkVarArgs,
    tkVirtual, tkWhile, tkWith, tkWrite, tkWriteOnly, tkXor, tkLineEnding);
  TTokens = set of TToken;
  TKeyWordTokens = set of tkAbsolute..tkXor;

  TShortSwitch = record
    FSwitch: char;
    FState: boolean;
  end;
  TShortSwitchList = array of TShortSwitch;
  TTextFormat = (tfAnsi, tfUnicode, tfUnicodeBigEndian, tfUtf8);

  TLineReader = class
  protected
    FIsUtf8: boolean;
    function GetCurLine: PChar; virtual; abstract;
  public
    function IsEOF: boolean; virtual; abstract;
    procedure ReadLine; virtual; abstract;
    property CurLine: PChar read GetCurLine;
    property IsUtf8: boolean read FIsUtf8;
  end;
  
  

  TFileLineReader = class(TLineReader)
  private
    FFileName: string;
    FFileHandle: THandle;
    FContent, FContentEnd: PAnsiChar;
    FSize: integer;
    FCurLine: PAnsiChar;
    fTextFormat: TTextFormat;
    FIsBigEndian: boolean;
    FEof: boolean;
    FHalfCrLn: boolean;
    FStrList: TFPList;
    FTempStr: ansistring;
    FBuffer: array[0..1025] of AnsiChar;
    function ParseTextFormat(Content: PAnsiChar; Size: Integer): TTextFormat;
    procedure ReadBuffer;
    procedure AddStr(P: PAnsiChar; Len: Integer);
    procedure ClearStr;
    function ConcatStr(Last: PAnsiChar; Size: Integer): AnsiString;
  protected
    function GetCurLine: PAnsiChar; override;
  public
    constructor Create(const AFileName: string);
    destructor Destroy; override;
    function IsEOF: boolean; override;
    procedure ReadLine; override;
    property FileName: string read FFileName;
  end;

  TStringLineReader = class(TLineReader)
  private
    FLines: TStringList;
    FIndex: integer;
    FCurLine: string;
    FEof: boolean;
  protected
    function GetCurLine: PChar; override;
  public
    constructor Create(const S: string);
    destructor Destroy; override;
    function IsEOF: boolean; override;
    procedure ReadLine; override;
  end;

  EScannerError = class(Exception);
  EFileNotFoundError = class(Exception);
  TScannerErrorEvent = procedure(const AMsg: string; AStop: boolean) of object;
  TDefineSymbolEvent = procedure(const S: string; DoDefine: boolean) of object;
  TIfDefinedEvent = procedure(const S: string; out IsDefined: boolean) of object;
  TIfEvalEvent = procedure(out Value: boolean) of object;
  TIfOptEvent = procedure(C: char; out isSet: boolean) of object;

  TDirectiveInfo = record
    Directive: TCompilerDirective;
    State: boolean;
    ArgStr1: string;
    ArgInt1, ArgInt2: integer;
  end;
  TDirectiveEvent = procedure(var DInfo: TDirectiveInfo) of object;
  TTokenValueKind = (tvkEmpty, tvkInt, tvkReal, tvkChr, tvkWChr);

  TTokenValue = record
    Kind: TTokenValueKind;
    case TTokenValueKind of
      tvkInt: (IntValue: int64);
      tvkReal: (RealValue: double);
  end;
  TCommentStyle = (cmsNone, cmsOldStyle, cmsNewStyle);

  TScanner = class
  private
    FCurSourceFile: TLineReader;
    FCurFileName: string;
    FCurRow: integer;
    FCurToken: TToken;
    FCurTokenString: string;
    FCurLine: PChar;
    FBuffer: PChar;
    FTokenStartRow: integer;
    FTokenStart: PChar;
    FIncludeStack: TFPList;
    FOnError: TScannerErrorEvent;
    FShortSwitches: TShortSwitchList;
    FKeyWords: TKeyWordTokens;
    FNestingComment: boolean;
    FNoReservedWord: boolean;
    FInDirective: TCommentStyle;
    FIFStateStack: array[1..32] of boolean;
    FIFCondIndex: integer;
    FCurDirective: TDirectiveInfo;
    FOnDirective: TDirectiveEvent;
    FOnIfDefined: TIfDefinedEvent;
    FOnIfEval: TIfEvalEvent;
    FOnIfOpt: TIfOptEvent;
    function GetTokenStartCol: integer;
    function OpenLineReader(const FileName: string): TLineReader;
    function GetCurColumn: integer;
    procedure PushFile;
    procedure PopFile;
    procedure Error(const Msg: string; Stop: boolean = False); overload;
    procedure Error(const Msg: string; Args: array of const; Stop: boolean = False); overload;
    function S2Int(S: PAnsiChar; Len: integer): int64;
    function S2Hex(S: PAnsiChar; Len: integer): int64;
    function S2Oct(S: PAnsiChar; Len: integer): int64;
    function S2Bin(S: PAnsiChar; Len: integer): int64;
    function S2Real(S: PAnsiChar; Len: integer): double;
  protected
    function DoFetchTextToken: TToken;
    function DoFetchToken: TToken;
    function DoFetchComment: TToken;
    function DoFetchCommentOldStyle: TToken;
    function DoFetchLine: boolean;
    procedure ProcessDirectives;
    procedure SkipTokens(var DInfo: TDirectiveInfo);
  public
    TimeStamp: TFileTimeStamp;
    TokenValue: TTokenValue;
    constructor Create;
    destructor Destroy; override;
    procedure Open(const S: string);
    procedure OpenFile(const AFileName: string);
    procedure OpenIncFile(const AFileName: string);
    function FetchToken: TToken;
    function ReadDirective(var DInfo: TDirectiveInfo): boolean; overload;
    procedure SkipWhiteSpace;
    function ReadFileStr: string;
    procedure SkipCurDirective;
    procedure EnableScopeKeyWords(Value: boolean);
    procedure EnableProcDirectives(Value: boolean);
    procedure EnablePropertyDirectives(Value: boolean);
    procedure EnableHintKeyWords(Value: boolean);
    procedure EnableLibraryKeyWord(Value: boolean);
    property NoReservedWord: boolean read FNoReservedWord write FNoReservedWord;
    property CurSwitches: TShortSwitchList read FShortSwitches;
    property CurSourceFile: TLineReader read FCurSourceFile;
    property CurFileName: string read FCurFileName;
    property CurLine: PChar read FCurLine;
    property CurRow: integer read FCurRow;
    property CurColumn: integer read GetCurColumn;
    property TokenStartRow: integer read FTokenStartRow;
    property TokenStartCol: integer read GetTokenStartCol;
    property CurToken: TToken read FCurToken;
    property CurTokenString: string read FCurTokenString;
    property OnError: TScannerErrorEvent read FOnError write FOnError;
    property OnDirective: TDirectiveEvent read FOnDirective write FOnDirective;
    property OnIfDefined: TIfDefinedEvent read FOnIfDefined write FOnIfDefined;
    property OnIfEval: TIfEvalEvent read FOnIfEval write FOnIfEval;
    property OnIfOpt: TIfOptEvent read FOnIfOpt write FOnIfOpt;
  end;

const
  TokenNames: array[TToken] of string =
    ('EOF', 'Whitespace', 'IllegalChar', 'Comment', 'Directive', 'DirectiveEnd', 'Identifier',
    'StrConst', 'CharConst', 'IntConst', 'HexConst', 'BinConst', 'OctalConst', 'FloatConst', '(',
    ')', '*', '+', ',', '-', '.', '/', ':', ';', '<', '=', '>', '@', '[', ']', '^', '\', '..',
    ':=', '<>', '<=', '>=', '**', '><', 'absolute', 'abstract', 'alias', 'and', 'array', 'as',
    'asm', 'assembler', 'begin', 'bitpacked', 'case', 'cdecl', 'class',
    'const', 'constructor', 'default', 'deprecated', 'destructor', 'dispid', 'dispinterface',
    'div', 'do', 'downto', 'dynamic', 'else', 'end', 'except', 'experimental', 'export', 'exports',
    'external', 'false', 'far', 'file', 'finalization', 'finally', 'for', 'forward', 'function',
    'goto', 'if', 'implementation', 'in', 'index', 'inherited', 'initialization', 'inline',
    'interface', 'is', 'label', 'library', 'local', 'message', 'mod', 'near', 'nil', 'nodefault',
    'not', 'object', 'of', 'on', 'operator', 'or', 'out', 'overload', 'override', 'packed', 'pascal',
    'platform', 'private', 'procedure', 'program', 'property', 'protected', 'public', 'published',
    'raise', 'read', 'readonly', 'record', 'register', 'reintroduce', 'repeat', 'resourcestring',
    'safecall', 'set', 'shl', 'shr', 'static', 'stdcall', 'stored', 'strict', 'string', 'then',
    'threadvar', 'to', 'true', 'try', 'type', 'unimplemented', 'unit', 'until', 'uses', 'var',
    'varargs', 'virtual', 'while', 'with', 'write', 'writeonly', 'xor', 'LineEnding');
  ScopeKeyWords: TKeyWordTokens = [tkPrivate, tkPublic, tkPublished, tkProtected, tkStrict];
  ProcDirectives: TKeyWordTokens = [tkVirtual, tkDynamic, tkAbstract, tkOverride, tkAlias,
    tkOverload, tkMessage, tkReintroduce, tkStatic, tkInline, tkAssembler, tkVarargs, tkLocal,
    tkDispId, tkExport, tkNear, tkFar, tkExternal, tkForward, tkCdecl, tkStdcall, tkRegister, tkPascal, tkSafecall];
  PropertyDirectives: TKeyWordTokens = [tkDefault, tkDispId, tkIndex, tkStored, tkNodefault,
    tkRead, tkReadOnly, tkWrite, tkWriteOnly];
  HintKeyWords: TKeyWordTokens = [tkPlatform, tkDeprecated, tkExperimental, tkUnimplemented];

implementation

uses fileutils;

const
  KeyWords: array
    [tkAbsolute..tkXor] of string = ('absolute', 'abstract', 'alias', 'and', 'array', 'as',
    'asm', 'assembler', 'begin', 'bitpacked', 'case', 'cdecl', 'class', 'const', 'constructor',
    'default', 'deprecated', 'destructor', 'dispid', 'dispinterface', 'div', 'do', 'downto',
    'dynamic', 'else', 'end', 'except', 'experimental', 'export', 'exports', 'external', 'false',
    'far', 'file', 'finalization', 'finally', 'for', 'forward', 'function', 'goto', 'if',
    'implementation', 'in', 'index', 'inherited', 'initialization', 'inline', 'interface', 'is',
    'label', 'library', 'local', 'message', 'mod', 'near', 'nil', 'nodefault', 'not', 'object',
    'of', 'on', 'operator', 'or', 'out', 'overload', 'override', 'packed', 'pascal', 'platform',
    'private', 'procedure', 'program', 'property', 'protected', 'public', 'published', 'raise', 'read', 'readonly',
    'record', 'register', 'reintroduce', 'repeat', 'resourcestring', 'safecall', 'set', 'shl',
    'shr', 'static', 'stdcall', 'stored', 'strict', 'string', 'then', 'threadvar', 'to', 'true',
    'try', 'type', 'unimplemented', 'unit', 'until', 'uses', 'var', 'varargs', 'virtual', 'while',
    'with', 'write', 'writeonly', 'xor');

function FindReservedWord(const S: string; out Token: TToken): boolean; overload;
type
  KeyList = array[0..999] of string;
  PKeyList = ^KeyList;
var
  L, H, I, C: integer;
  FList: PKeyList;
begin
  Result := False;
  FList := PKeyList(@KeyWords);
  Token := tkIdentifier;
  L := 0;
  H := Length(KeyWords) - 1;
  while L <= H do
  begin
    I := (L + H) shr 1;
    C := CompareText(FList^[I], S);
    if C < 0 then
      L := I + 1
    else
    begin
      H := I - 1;
      if C = 0 then
      begin
        Result := True;
        Token := TToken(Ord(Low(KeyWords)) + I);
        Break;
      end;
    end;
  end;
end;

function FindReservedWord(const S: PAnsiChar; Len: integer; out Token: TToken): boolean; overload;
type
  KeyList = array
    [0..999] of string;
  PKeyList = ^KeyList;
var
  L, H, I, C, MaxLen: integer;
  FList: PKeyList;
begin
  Result := False;
  FList := PKeyList(@KeyWords);
  Token := tkIdentifier;
  L := 0;
  H := Length(KeyWords) - 1;
  while L <= H do
  begin
    I := (L + H) shr 1;
    MaxLen := Length(FList^[I]);
    if MaxLen < Len then
      MaxLen := Len;
    C := StrLIComp(PAnsiChar(FList^[I]), S, MaxLen);
    if C < 0 then
      L := I + 1
    else
    begin
      H := I - 1;
      if C = 0 then
      begin
        Result := True;
        Token := TToken(Ord(Low(KeyWords)) + I);
        Break;
      end;
    end;
  end;
end;

function IsBigEndian: boolean;
var
  W: word;
begin
  W := $0102;
  Result := PByte(@W)^ = 1;
end;

function StrP2Int(S: PAnsiChar; Len: integer; out OkFlag: boolean): int64;
var
  dig: integer;
begin
  OkFlag := False;
  Result := 0;
  if Len = 0 then
    Exit;
  dig := 0;
  while Len > 0 do
  begin
    case S^ of
      '0'..'9': dig := Ord(S^) - Ord('0');
      else
        Break;
    end;
    if Result > (High(Result) div 10) then
    begin
      OkFlag := False;
      Exit;
    end;
    Result := Result * 10 + dig;
    Dec(Len);
    Inc(S);
  end;
  OkFlag := True;
end;

function StrP2Hex(S: PAnsiChar; Len: integer; out OkFlag: boolean): int64;
var
  dig: integer;
begin
  OkFlag := False;
  Result := 0;
  if Len = 0 then
    Exit;
  dig := 0;
  while Len > 0 do
  begin
    case S^ of
      '0'..'9': dig := Ord(S^) - Ord('0');
      'A'..'F': dig := Ord(S^) - (Ord('A') - 10);
      'a'..'f': dig := Ord(S^) - (Ord('a') - 10);
      else
        Break;
    end;
    if Result and $f000000000000000 <> 0 then
    begin
      OkFlag := False;
      Exit;
    end;
    Result := Result shl 4 + dig;
    Dec(Len);
    Inc(S);
  end;
  OkFlag := True;
end;

function StrP2Oct(S: PAnsiChar; Len: integer; out OkFlag: boolean): int64;
var
  dig: integer;
begin
  OkFlag := False;
  Result := 0;
  if Len = 0 then
    Exit;
  dig := 0;
  while Len > 0 do
  begin
    case S^ of
      '0'..'7': dig := Ord(S^) - Ord('0');
      else
        Break;
    end;
    if Result and $e000000000000000 <> 0 then
    begin
      OkFlag := False;
      Exit;
    end;
    Result := Result shl 3 + dig;
    Dec(Len);
    Inc(S);
  end;
  OkFlag := True;
end;

function StrP2Bin(S: PAnsiChar; Len: integer; out OkFlag: boolean): int64;
var
  dig: integer;
begin
  OkFlag := False;
  Result := 0;
  if Len = 0 then
    Exit;
  dig := 0;
  while Len > 0 do
  begin
    case S^ of
      '0'..'1': dig := Ord(S^) - Ord('0');
      else
        Break;
    end;
    if Result and $8000000000000000 <> 0 then
    begin
      OkFlag := False;
      Exit;
    end;
    Result := Result shl 1 + dig;
    Dec(Len);
    Inc(S);
  end;
  OkFlag := True;
end;

type
  TIncludeStackItem = class
  public
    SourceFile: TLineReader;
    FileName: string;
    Token: TToken;
    TokenString: string;
    Buffer: PChar;
    Line: PChar;
    Row: integer;
  end;

procedure TFileLineReader.AddStr(P: PAnsiChar; Len: Integer);
var
  S: AnsiString;
begin
  if FStrList = nil then
  begin
    FStrList := TFPList.Create;
    FStrList.Capacity := 128;
  end;
  SetString(S, P, Len);
  FStrList.Add(Pointer(S));
  Pointer(S) := nil;
end;

{$push}
{$warn 5027 off}
procedure TFileLineReader.ClearStr;
var
  i: Integer;
  p: Pointer;
begin
  for i := 0 to FStrList.Count - 1 do
  begin
    p := FStrList[i];
    AnsiString(p) := '';
  end;
  FStrList.Count := 0;
end;
{$pop}

function TFileLineReader.ConcatStr(Last: PAnsiChar;
  Size: Integer): AnsiString;
var
  len, i, p: Integer;
  s: Pointer;
begin
  len := 0;
  for i := 0 to FStrList.Count - 1 do
    len := len + Length(AnsiString(FStrList[i]));
  len := len + Size;
  SetLength(Result, len);
  p := 1;
  for i := 0 to FStrList.Count - 1 do
  begin
    s := FStrList[i];
    len := Length(AnsiString(s));
    Move(s^, Result[p], len);
    Inc(p, len);
  end;
  Move(Last^, Result[p], Size);
end;

constructor TFileLineReader.Create(const AFileName: string);
begin
  FIsBigEndian := IsBigEndian;
  FFileName := AFilename;
  FFileHandle := FileOpen(AFileName, fmOpenRead or fmShareDenyNone);
  if FFileHandle = THandle(-1) then
    SysUtils.RaiseLastOSError;
  ReadBuffer;
  FTextFormat := ParseTextFormat(@fBuffer[0], fSize);
  if fTextFormat = tfUtf8 then
    Inc(FContent, 3)
  else if FTextFormat in [tfUnicode, tfUnicodeBigEndian] then
    Inc(FContent, 2);
  FEof := False;
  FIsUtf8 := fTextFormat in [tfUtf8, tfUnicode, tfUnicodeBigEndian];
end;

destructor TFileLineReader.Destroy;
begin
  if FFileHandle <> THandle(-1) then
    FileClose(FFileHandle);
  FStrList.Free;
  inherited Destroy;
end;

function TFileLineReader.GetCurLine: PAnsiChar;
begin
  Result := FCurLine;
end;

function TFileLineReader.IsEOF: boolean;
begin
  Result := FEof;
end;

function TFileLineReader.ParseTextFormat(Content: PAnsiChar; Size: integer): TTextFormat;
begin
  if Size > 1 then
    if (Content[0] = #$ff) and (Content[1] = #$fe) then
      Result := tfUnicode
    else if (Content[0] = #$fe) and (Content[1] = #$ff) then
      Result := tfUnicodeBigEndian
    else if (Content[0] = #$ef) and (Content[1] = #$bb) and (Content[2] = #$bf) then
      Result := tfUtf8
    else
      Result := tfAnsi
  else
    Result := tfAnsi;
end;

procedure TFileLineReader.ReadBuffer;
begin
  FSize := FileRead(FFileHandle, FBuffer[0], SizeOf(fBuffer) - 2);
  if FSize < 0 then
    SysUtils.RaiseLastOSError;
  FEof := FSize = 0;
  FContent := @FBuffer[0];
  FContentEnd := FContent + FSize;
end;

procedure TFileLineReader.ReadLine;

  function ReadAnsi(var Start: PAnsiChar; var Len: integer): boolean;
  var
    c: AnsiChar;
  begin
    if FSize = 0 then
    begin
      Result := True;
      Len := 0;
      Exit;
    end;
    if FHalfCrLn and (FContent^ = #10) then
    begin
      Inc(FContent);
      FHalfCrLn := False;
    end;
    Start := FContent;
    while FContent < FContentEnd do
    begin
      if FContent^ in [#13, #10] then
      begin
        c := FContent^;
        FContent^ := #0;
        Len := FContent - Start;
        Inc(FContent);
        FHalfCrLn := (FContent = FContentEnd) and (c = #13);
        if (c = #13) and (FContent^ = #10) then
          Inc(FContent);
        Result := True;
        Exit;
      end
      else
        Inc(FContent);
    end;
    Result := False;
    Len := FContent - Start;
  end;

  function ReadWide(var Start: PAnsiChar; var Len: integer): boolean;
  var
    P, PEnd: PWideChar;
    c: widechar;
  begin
    if FSize = 0 then
    begin
      Result := True;
      Len := 0;
      Exit;
    end;
    P := PWideChar(FContent);
    PEnd := PWideChar(FContentEnd);
    if FHalfCrLn and (P^ = #10) then
    begin
      Inc(P);
      FHalfCrLn := False;
    end;
    Start := PAnsiChar(P);
    while P < PEnd do
    begin
      if (P^ = #13) or (P^ = #10) then
      begin
        c := P^;
        P^ := #0;
        Len := PAnsiChar(P) - Start;
        Inc(P);
        FHalfCrLn := (P = PEnd) and (c = #13);
        if (c = #13) and (P^ = #10) then
          Inc(P);
        Result := True;
        FContent := PAnsiChar(P);
        Exit;
      end
      else
        Inc(P);
    end;
    FContent := PAnsiChar(P);
    Result := False;
    Len := PAnsiChar(P) - Start;
  end;

  function ReadWideSwap(out Start: PAnsiChar; out Len: integer): boolean;
  var
    P, PEnd: PWideChar;
    b: AnsiChar;
    c: widechar;
  begin
    if FSize = 0 then
    begin
      Result := True;
      Len := 0;
      Exit;
    end;
    P := PWideChar(FContent);
    PEnd := PWideChar(FContentEnd);
    if FHalfCrLn and (P^ = #$0a00) then
    begin
      Inc(P);
      FHalfCrLn := False;
    end;
    Start := PAnsiChar(P);
    while P < PEnd do
    begin
      b := PAnsiChar(P)^;
      PAnsiChar(P)^ := PAnsiChar(P)[1];
      PAnsiChar(P)[1] := b;
      if (P^ = #13) or (P^ = #10) then
      begin
        c := P^;
        P^ := #0;
        Len := PAnsiChar(P) - Start;
        Inc(P);
        FHalfCrLn := (P = PEnd) and (c = #13);
        if (c = #13) and (P^ = #$0a00) then
          Inc(P);
        Result := True;
        FContent := PAnsiChar(P);
        Exit;
      end
      else
        Inc(P);
    end;
    FContent := PAnsiChar(P);
    Result := False;
    Len := PAnsiChar(P) - Start;
  end;

  procedure ToUtf8(WBuf: PWideChar; WChars: integer; out S: ansistring);
  var
    Size: integer;
  begin
    if WChars = 0 then S := ''
    else
    begin
      Size := UnicodeToUtf8(nil, 0, WBuf, WChars);
      SetLength(S, Size - 1);
      UnicodeToUtf8(PAnsiChar(S), Size, WBuf, WChars);
    end;
  end;

  procedure ToUtf8_2(var TempStr: string);
  var
    S: ansistring;
  begin
    ToUtf8(pWideChar(Pointer(TempStr)), Length(TempStr) div 2, S);
    TempStr := S;
  end;

  procedure Read;
  var
    Start: PAnsiChar;
    Len: integer;
    Multi, Ok: boolean;
  label
    1;
  begin
    Multi := False;
    1:
      case FTextFormat of
        tfUnicode: if Self.FIsBigEndian then
            Ok := ReadWideSwap(Start, Len)
          else
            Ok := ReadWide(Start, Len);
        tfUnicodeBigEndian: if Self.FIsBigEndian then
            Ok := ReadWide(Start, Len)
          else
            Ok := ReadWideSwap(Start, Len);
        else
          Ok := ReadAnsi(Start, Len);
      end;
    if not Ok then
    begin
      Multi := True;
      AddStr(Start, Len);
      ReadBuffer;
      goto 1;
    end
    else
    if Multi then
    begin
      FTempStr := ConcatStr(Start, Len);
      if FTextFormat in [tfUnicode, tfUnicodeBigEndian] then
      begin
        ToUtf8_2(FTempStr);
        FCurLine := PAnsiChar(FTempStr);
      end
      else
        FCurLine := PAnsiChar(FTempStr);
      ClearStr;
    end
    else
    begin
      if FTextFormat in [tfUnicode, tfUnicodeBigEndian] then
      begin
        ToUtf8(PWideChar(Start), Len div 2, FTempStr);
        FCurLine := PAnsiChar(FTempStr);
      end
      else
        FCurLine := Start;
    end;
  end;

begin
  FCurLine := nil;
  if FContent >= FContentEnd then
    ReadBuffer;
  if FEof then
    Exit;
  FTempStr := '';
  Read;
end;

constructor TScanner.Create;
begin
  FIncludeStack := TFPList.Create;
  FKeyWords := [tkAbsolute..tkXor];
  FKeyWords := FKeyWords - HintKeyWords;
  FKeyWords := FKeyWords - ProcDirectives;
  FKeyWords := FKeyWords - ScopeKeyWords;
  FKeyWords := FKeyWords - PropertyDirectives;
end;

destructor TScanner.Destroy;
begin
  while FIncludeStack.Count > 1 do
  begin
    TLineReader(FIncludeStack[1]).Free;
    FIncludeStack.Delete(1);
  end;
  FIncludeStack.Free;
  CurSourceFile.Free;
  inherited Destroy;
end;

function TScanner.DoFetchComment: TToken;
var
  NestingLevel: integer;
begin
  NestingLevel := 0;
  while (FCurLine[0] <> '}') or (NestingLevel > 0) do
  begin
    if FCurLine[0] = #0 then
    begin
      if not DoFetchLine then
      begin
        Error(SErrUnexpectedEOFInComment, True);
        Result := tkEOF;
        Exit;
      end;
    end
    else
    begin
      if FNestingComment and (FCurLine[0] = '{') then
        Inc(NestingLevel)
      else if FCurLine[0] = '}' then
        Dec(NestingLevel);
      Inc(FCurLine);
    end;
  end;
  Inc(FCurLine);
  Result := tkComment;
end;

function TScanner.DoFetchCommentOldStyle: TToken;
begin
  while (FCurLine[0] <> '*') or (FCurLine[1] <> ')') do
  begin
    if FCurLine[0] = #0 then
    begin
      if not DoFetchLine then
      begin
        Error(SErrUnexpectedEOFInComment, True);
        Result := tkEOF;
        Exit;
      end;
    end
    else
      Inc(FCurLine);
  end;
  Inc(FCurLine, 2);
  Result := tkComment;
end;

function TScanner.DoFetchLine: boolean;
begin
  if FCurSourceFile.IsEOF then
  begin
    FCurLine := nil;
    FBuffer := nil;
    Result := False;
  end
  else
  begin
    FCurSourceFile.ReadLine;
    FCurLine := FCurSourceFile.CurLine;
    FBuffer := FCurLine;
    Result := FCurLine <> nil;
    Inc(FCurRow);
  end;
end;

function TScanner.DoFetchTextToken: TToken;
var
  Start: PAnsiChar;
  Len, OldLength, Quoted, I: integer;
  C: AnsiChar;
begin
  Result := tkEOF;
  FCurTokenString := '';
  while True do
  begin
    case FCurLine[0] of
      '#':
      begin
        Inc(FCurLine);
        if FCurLine[0] = '$' then
        begin
          Inc(
            FCurLine);
          Start := FCurLine;
          while FCurLine[0] in ['0'..'9', 'A'..'F', 'a'..'f'] do
            Inc(FCurLine);
          Len := FCurLine - Start;
          if Len = 0 then
            Error(SErrInvalidCharConst);
          C := Chr(S2Hex(Start, Len) mod 256);
        end
        else
        begin
          Start := FCurLine;
          while FCurLine[0] in ['0'..'9'] do
            Inc(
              FCurLine);
          Len := FCurLine - Start;
          if Len = 0 then
            Error(SErrInvalidCharConst);
          C := Chr(S2Int(Start, Len) mod 256);
        end;
        Len := Length(FCurTokenString) + 1;
        SetLength(FCurTokenString,
          Len);
        FCurTokenString[Len] := C;
        if Result = tkEOF then
          Result := tkCharConst
        else
          Result := tkStrConst;
      end;
      '''':
      begin
        Quoted := 0;
        Inc(FCurLine);
        Start := FCurLine;
        while FCurLine[0] <> #0 do
        begin
          if FCurLine[0] = '''' then
          begin
            if FCurLine[1] = '''' then
            begin
              Inc(
                Quoted);
              Inc(FCurLine, 2);
            end
            else
              Break;
          end
          else
            Inc(FCurLine);
        end;
        Len := FCurLine - Start;
        if Len > 0 then
        begin
          if Quoted > 0 then
          begin
            Dec(Len, Quoted);
            OldLength := Length(FCurTokenString);
            SetLength(FCurTokenString, Len + OldLength);
            for I := OldLength + 1 to Length(FCurTokenString) do
            begin
              FCurTokenString[I] := Start^;
              if Start^ = '''' then
                Inc(Start, 2)
              else
                Inc(Start);
            end;
          end
          else
          begin
            OldLength := Length(FCurTokenString);
            SetLength(FCurTokenString, Len + OldLength);
            Move(Start^, FCurTokenString[OldLength + 1], Len);
          end;
        end;
        if FCurLine[0] <> #0 then
          Inc(FCurLine)
        else
          Error(SErrOpenString);
        Result := tkStrConst;
      end;
      else
        Break;
    end;
  end;
end;

function TScanner.DoFetchToken: TToken;
var
  Start: PChar;
  Len: integer;
  IsDirective: boolean;
label
  FetchStart;
begin
  if FCurLine = nil then
    if not DoFetchLine then
    begin
      Result := tkEOF;
      FCurToken := Result;
      Exit;
    end;
  FCurTokenString := '';
  Result := tkEof;
  FetchStart:
    FTokenStart := FCurLine;
  FTokenStartRow := FCurRow;
  case FCurLine[0] of
    #0:
    begin
      if DoFetchLine then
        goto FetchStart;
    end;
    ' ', #9:
    begin
      repeat
        Inc(FCurLine);
        if FCurLine[0] = #0 then
          if not DoFetchLine then
          begin
            FCurToken := Result;
            Exit;
          end;
      until not (FCurLine[0] in [' ', #9]);
      goto FetchStart;
    end;
    '#', '''': Result := DoFetchTextToken;
    '&': if FCurLine[1] in ['a'..'b', 'A'..'Z', '_'] then
      begin
        Inc(FCurLine);
        Start := FCurLine;
        repeat
          Inc(FCurLine);
        until not (FCurLine[0] in ['A'..'Z', 'a'..'z', '0'..'9', '_']);
        Len := FCurLine - Start;
        if Len > 0 then
          SetString(FCurTokenString, Start, Len);
        Result := tkIdentifier;
      end
      else
      begin
        Inc(FCurLine);
        Start := FCurLine;
        while FCurLine[0] in ['0'..'7'] do
          Inc(FCurLine);
        Len :=
          FCurLine - Start;
        if Len = 0 then
          Error(SErrInvalidOctalConst);
        TokenValue.IntValue := S2Oct(Start, Len);
        TokenValue.Kind := tvkInt;
        Result := tkOctalConst;
      end;
    '$':
    begin
      Inc(FCurLine);
      Start := FCurLine;
      while FCurLine[0] in ['0'..'9', 'A'..'F', 'a'..'f'] do
        Inc(FCurLine);
      Len := FCurLine - Start;
      if Len = 0 then
        Error(SErrInvalidHexConst);
      TokenValue.IntValue := S2Hex(Start, Len);
      TokenValue.Kind := tvkInt;
      Result := tkHexConst;
    end;
    '%':
    begin
      Inc(FCurLine);
      Start := FCurLine;
      while FCurLine[0] in ['0', '1'] do
        Inc(FCurLine);
      Len := FCurLine - Start;
      if Len = 0 then
        Error(SErrInvalidBinConst);
      TokenValue.IntValue := S2Bin(Start, Len);
      TokenValue.Kind := tvkInt;
      Result := tkBinConst;
    end;
    '(':
    begin
      Inc(FCurLine);
      if FCurLine[0] = '*' then
      begin
        Inc(FCurLine);
        IsDirective := (FCurLine[0] = '$');
        if IsDirective then
        begin
          Inc(
            FCurLine);
          FInDirective := cmsOldStyle;
          ProcessDirectives;
          goto FetchStart;
        end
        else
        begin
          DoFetchCommentOldStyle;
          goto FetchStart;
        end;
      end
      else
        Result := tkBraceOpen;
    end;
    ')':
    begin
      Inc(FCurLine);
      Result := tkBraceClose;
    end;
    '*':
    begin
      Inc(FCurLine);
      if FCurLine[0] = '*' then
      begin
        Inc(FCurLine);
        Result := tkPower;
      end
      else if (FCurLine[0] = ')') and (FInDirective = cmsOldStyle) then
      begin
        Inc(FCurLine);
        FInDirective := cmsNone;
        Result := tkDirectiveEnd;
      end
      else
        Result := tkMul;
    end;
    '+':
    begin
      Inc(FCurLine);
      Result := tkPlus;
    end;
    ',':
    begin
      Inc(FCurLine);
      Result := tkComma;
    end;
    '-':
    begin
      Inc(FCurLine);
      Result := tkMinus;
    end;
    '.':
    begin
      Inc(FCurLine);
      if FCurLine[0] = '.' then
      begin
        Inc(FCurLine);
        Result := tkDotDot;
      end
      else
        Result := tkDot;
    end;
    '/':
    begin
      Inc(FCurLine);
      if FCurLine[0] = '/' then
      begin
        while
          FCurLine[0] <> #0 do
          Inc(FCurLine);
        goto FetchStart;
      end
      else
        Result := tkFDiv;
    end;
    '0'..
    '9':
    begin
      Start := FCurLine;
      Inc(FCurLine);
      while FCurLine[0] in ['0'..'9'] do
        Inc(FCurLine);
      if FCurLine[0] = '.' then
      begin
        if FCurLine[1] = '.' then
        begin
          Result := tkIntConst;
        end
        else
        begin
          Inc(FCurLine);
          while FCurLine[0] in ['0'..'9'] do
            Inc(FCurLine);
          if FCurLine[0] in ['E', 'e'] then
          begin
            Inc(FCurLine);
            if FCurLine[0] in ['+', '-'] then
              Inc(FCurLine);
            if not (FCurLine[0] in ['0'..'9']) then
              Error(SErrInvalidRealConst);
            while FCurLine[0] in ['0'..'9'] do
              Inc(FCurLine);
          end;
          Result := tkFloatConst;
        end;
      end
      else
        Result := tkIntConst;
      Len := FCurLine - Start;
      if Result = tkIntConst then
      begin
        TokenValue.IntValue := S2Int(Start, Len);
        TokenValue.Kind := tvkInt;
      end
      else
      begin
        TokenValue.RealValue := S2Real(Start, Len);
        TokenValue.Kind := tvkReal;
      end;
    end;
    ':':
    begin
      Inc(FCurLine);
      if FCurLine[0] = '=' then
      begin
        Inc(FCurLine);
        Result := tkAssign;
      end
      else
        Result := tkColon;
    end;
    ';':
    begin
      Inc(FCurLine);
      Result := tkSemicolon;
    end;
    '<':
    begin
      Inc(FCurLine);
      if FCurLine[0] = '>' then
      begin
        Inc(FCurLine);
        Result := tkNotEqual;
      end
      else if FCurLine[0] = '=' then
      begin
        Inc(FCurLine);
        Result := tkLessEqualThan;
      end
      else
        Result := tkLessThan;
    end;
    '=':
    begin
      Inc(FCurLine);
      Result := tkEqual;
    end;
    '>':
    begin
      Inc(FCurLine);
      if FCurLine[0] = '=' then
      begin
        Inc(FCurLine);
        Result := tkGreaterEqualThan;
      end
      else if FCurLine[0] = '<' then
      begin
        Inc(FCurLine);
        Result := tkSymmetricalDifference;
      end
      else
        Result := tkGreaterThan;
    end;
    '@':
    begin
      Inc(
        FCurLine);
      Result := tkAt;
    end;
    '[':
    begin
      Inc(FCurLine);
      Result := tkSquaredBraceOpen;
    end;
    ']':
    begin
      Inc(FCurLine);
      Result := tkSquaredBraceClose;
    end;
    '^':
    begin
      Inc(FCurLine);
      Result := tkCaret;
    end;
    '\':
    begin
      Inc(FCurLine);
      Result := tkBackslash;
    end;
    '{':
    begin
      Inc(FCurLine);
      IsDirective := FCurLine[0] = '$';
      if IsDirective then
      begin
        Inc(FCurLine);
        FInDirective := cmsNewStyle;
        ProcessDirectives;
        goto FetchStart;
      end
      else
      begin
        DoFetchComment;
        goto FetchStart;
      end;
    end;
    '}':
    begin
      if FInDirective = cmsNewStyle then
      begin
        Result := tkDirectiveEnd;
        FIndirective := cmsNone;
      end
      else
      begin
        Error(SErrInvalidCharacter, [FCurLine[0]]);
        Result := tkIllegalChar;
      end;
      Inc(FCurLine);
    end;
    'A'..'Z', 'a'..'z', '_':
    begin
      Start := FCurLine;
      repeat
        Inc(FCurLine);
      until not (FCurLine[0] in ['A'..'Z', 'a'..'z', '0'..'9', '_']);
      Len := FCurLine - Start;
      if not FNoReservedWord and FindReservedWord(Start, Len, Result) then
      begin
        if Result in FKeyWords then
        begin
          FCurToken := Result;
          Exit;
        end;
      end;
      SetString(
        FCurTokenString, Start, Len);
      Result := tkIdentifier;
    end;
    else
      Error(SErrInvalidCharacter, [FCurLine^]);
      Result := tkIllegalChar;
      Inc(FCurLine);
      goto FetchStart;
  end;
  FCurToken :=
    Result;
end;

procedure TScanner.EnableHintKeyWords(Value: boolean);
begin
  if Value then
    FKeyWords := FKeyWords + HintKeyWords
  else
    FKeyWords := FKeyWords - HintKeyWords;
end;

procedure TScanner.EnableLibraryKeyWord(Value: boolean);
begin
  if Value then
    Include(FKeyWords, tkLibrary)
  else
    Exclude(FKeyWords, tkLibrary);
end;

procedure TScanner.EnableProcDirectives(Value: boolean);
begin
  if Value then
    FKeyWords := FKeyWords + ProcDirectives
  else
    FKeyWords := FKeyWords - ProcDirectives;
end;

procedure TScanner.EnablePropertyDirectives(Value: boolean);
begin
  if Value then
    FKeyWords := FKeyWords + PropertyDirectives
  else
    FKeyWords := FKeyWords - PropertyDirectives;
end;

procedure TScanner.EnableScopeKeyWords(Value: boolean);
begin
  if Value then
    FKeyWords := FKeyWords + ScopeKeyWords
  else
    FKeyWords := FKeyWords - ScopeKeyWords;
end;

procedure TScanner.Error(const Msg: string; Args: array of const; Stop: boolean);
begin
  Error(Format(Msg, Args), Stop);
end;

procedure TScanner.Error(const Msg: string; Stop: boolean);
begin
  if Assigned(FOnError) then
    FOnError(Msg, Stop)
  else
    raise
    EScannerError.Create(Msg);
end;

function TScanner.FetchToken: TToken;
begin
  Result := tkEOF;
  while True do
  begin
    Result := DoFetchToken;
    if FCurToken = tkEOF then
    begin
      if FIncludeStack.Count > 0 then
      begin
        PopFile;
        Result := FCurToken;
      end
      else
        Break;
    end
    else
      Break;
  end;
end;

function TScanner.GetCurColumn: integer;
begin
  Result := FCurLine - FBuffer;
end;

function TScanner.GetTokenStartCol: integer;
begin
  Result := FTokenStart - FBuffer;
end;

procedure TScanner.Open(const S: string);
begin
  FCurSourceFile := TStringLineReader.Create(S);
  FCurFileName := '';
  FCurRow := 0;
end;

procedure TScanner.OpenFile(const AFileName: string);
begin
  FCurSourceFile := OpenLineReader(AFileName);
  FCurFileName := AFileName;
  FCurRow := 0;
  GetFileTimeStamp(AFileName, TimeStamp);
end;

procedure TScanner.OpenIncFile(const AFileName: string);
begin
  PushFile;
  FCurSourceFile := OpenLineReader(AFileName);
  FCurFileName := AFileName;
  FCurRow := 0;
end;

function TScanner.OpenLineReader(const FileName: string): TLineReader;
begin
  if not FileExists(FileName) then
    Error(SErrFileNotFound, [ExtractFileName(FileName)], True);
  try
    Result := TFileLineReader.Create(FileName);
  except
    Result := nil;
    Error(SErrFileOpenFailed, [ExtractFileName(FileName)], True);
  end;
end;

procedure TScanner.PopFile;
var
  Item: TIncludeStackItem;
begin
  if FIncludeStack.Count > 0 then
  begin
    FCurSourceFile.Free;
    Item := TIncludeStackItem(FIncludeStack[FIncludeStack.Count - 1]);
    FIncludeStack.Delete(FIncludeStack.Count - 1);
    FCurSourceFile := Item.SourceFile;
    FCurFileName := Item.FileName;
    FCurToken := Item.Token;
    FCurTokenString := Item.TokenString;
    FCurRow := Item.Row;
    FCurLine := Item.Line;
    FBuffer :=
      Item.Buffer;
    Item.Free;
  end;
end;

procedure TScanner.ProcessDirectives;
var
  More: boolean;
begin
  repeat
    More := ReadDirective(FCurDirective);
    if Assigned(FOnDirective) then
      FOnDirective(FCurDirective);
  until not More;
  SkipCurDirective;
end;

procedure TScanner.PushFile;
var
  Item: TIncludeStackItem;
begin
  Item := TIncludeStackItem.Create;
  Item.SourceFile := CurSourceFile;
  Item.FileName := CurFileName;
  Item.Token := CurToken;
  Item.TokenString := CurTokenString;
  Item.Line := FCurLine;
  Item.Row := FCurRow;
  Item.Buffer := FBuffer;
  FIncludeStack.Add(Item);
end;

function TScanner.ReadDirective(var DInfo: TDirectiveInfo): boolean;

  procedure ProcessResource(var DInfo: TDirectiveInfo);
  begin
    SkipWhiteSpace;
    DInfo.ArgStr1 := ReadFileStr;
    DInfo.Directive := cdResource;
  end;

  procedure ProcessInclude(var DInfo: TDirectiveInfo);
  begin
    SkipWhiteSpace;
    DInfo.ArgStr1 := ReadFileStr;
    DInfo.Directive := cdInclude;
  end;

  procedure InvalidErr(S: PAnsiChar; Len: integer);
  var
    Name: string;
  begin
    SetString(Name, S, Len);
    Error(SErrInvalidDirective, [Name]);
  end;

const
  DStr: array[0..26] of string = (
    'ALIGN', 'APPTYPE', 'BOOLEVAL', 'DEFINE', 'ELSE', 'ELSEIF', 'ENDIF', 'EXTERNALSYM', 'HPPEMIT',
    'IF', 'IFDEF', 'IFEND', 'IFNDEF', 'IFOPT', 'INCLUDE', 'IOCHECKS', 'MINENUMSIZE', 'MODE',
    'NODEFINE', 'OVERFLOWCHECKS', 'RANGECHECKS', 'RESOURCE', 'SAFEDIVIDE', 'TYPEDADDRESS',
    'TYPEINFO', 'UNDEF', 'WRITEABLECONST');
  Directives: array[0..26] of TCompilerDirective = (cdAlign, cdAppType, cdBoolEval, cdDefine, cdElse,
    cdElseIf, cdEndIf, cdExternalSym, cdHPPEmit, cdIf, cdIfDef, cdIfEnd, cdIfNDef, cdIfOpt,
    cdInclude, cdIOChecks, cdMinEnumSize, cdMode,
    cdNoDefine, cdOverflowChecks, cdRangeChecks, cdResource, cdSafeDivide, cdTypedAddress,
    cdTypeInfo, cdUndef, cdWriteableConst);

  function Max(I1, I2: integer): integer;
  begin
    if I1 > I2 then
      Result := I1
    else
      Result := I2;
  end;

  function FindDirective(const S: PAnsiChar; Len: integer; out Directive: TCompilerDirective): boolean;
  var
    L, H, I, C: integer;
    OldChar: char;
  begin
    OldChar := S[Len];
    S[Len] := #0;
    Result := False;
    L := 0;
    H := Length(DStr) - 1;
    while
      L <= H do
    begin
      I := (L + H) shr 1;
      C := StrLIComp(PAnsiChar(DStr[I]), S, Max(Len, Length(DStr[I])));
      if C < 0 then
        L := I + 1
      else
      begin
        H := I - 1;
        if C = 0 then
        begin
          Result := True;
          Directive := Directives[I];
          Break;
        end;
      end;
    end;
    S[Len] := OldChar;
  end;

  function GetToken(out Start: PAnsiChar; out Len: integer): TToken;
  label
    DoScan;
  begin
    Result := tkEof;
    if FCurLine = nil then
      if not DoFetchLine then
        Exit;
    DoScan:
      case FCurLine[0] of
        #0: if DoFetchLine then
            goto DoScan;
        #32, #9:
        begin
          repeat
            Inc(FCurLine);
            if FCurLine[0] = #0 then
              if not DoFetchLine then
                Exit;
          until not (FCurLine[0] in [#32, #9]);
          goto DoScan;
        end;
        '0'..'9':
        begin
          Start :=
            FCurLine;
          repeat
            Inc(FCurLine);
          until not (FCurLine[0] in ['0'..'9']);
          Len := FCurLine - Start;
          Result := tkIntConst;
        end;
        'A'..'Z', 'a'..'z', '_':
        begin
          Start := FCurLine;
          repeat
            Inc(FCurLine);
          until not (FCurLine[0] in ['A'..'Z', 'a'..'z', '0'..'9', '_']);
          Len := FCurLine - Start;
          Result := tkIdentifier;
        end;
      end;
  end;

  function SameStr(S1: PAnsiChar; Len1: integer; const S2: string): boolean;
  begin
    if Length(S2) = Len1 then
      Result := StrLIComp(S1, PAnsiChar(S2), Len1) = 0
    else
      Result := False;
  end;

  function GetState: boolean;
  var
    Start: PAnsiChar;
    Len: integer;
  begin
    GetToken(Start, Len);
    if SameStr(Start, Len, 'on') then
      Result := True
    else if SameStr(Start, Len, 'off') then
      Result := False
    else
    begin
      Error(SErrInvalidDirectiveParam, True);
      Result := False;
    end;
  end;

  function GetIdent: string;
  var
    Start: PAnsiChar;
    Len: integer;
  begin
    if GetToken(Start, Len) = tkIdentifier then
      SetString(Result, Start, Len)
    else
      Result := '';
  end;

  procedure ProcessLong(Dir: TCompilerDirective; var DInfo: TDirectiveInfo); overload;

    function IfEval: boolean;
    begin
      Self.FOnIfEval(Result);
    end;

    procedure GetOpt(var C: AnsiChar; State: boolean);
    begin
    end;

  label
    1;
  var
    Start: PAnsiChar;
    Len: integer;
    Al: int64;
    IsDefined: boolean;
  begin
    DInfo.Directive := Dir;
    1:
      case Dir of
        cdBoolEval, cdIOChecks, cdOverflowChecks, cdRangeChecks, cdSafeDivide, cdTypeInfo,
        cdTypedAddress, cdWriteableConst:
        begin
          DInfo.State := GetState;
        end;
        cdAppType: DInfo.ArgStr1 := GetIdent;
        cdAlign: case GetToken(Start, Len) of
            tkIdentifier: if SameStr(Start, Len, 'on') then
                DInfo.State := True
              else
              if SameStr(Start, Len, 'off') then
                DInfo.State := False
              else
                Error(SErrInvalidDirectiveParam, True);
            tkIntConst:
            begin
              AL := S2Int(Start, Len);
              if AL in [1, 2, 4, 8, 16, 32] then
                DInfo.ArgInt1 := AL
              else
                Error(SErrInvalidDirectiveParam, True);
            end;
            else
              Error(SErrInvalidDirectiveParam, True);
          end;
        cdMinEnumSize: case GetToken(Start, Len) of
            tkIntConst:
            begin
              AL := S2Int(Start, Len);
              if AL in [1, 2, 4] then
                DInfo.ArgInt1 := AL
              else
                Error(SErrInvalidDirectiveParam,
                True);
            end;
            else
              Error(SErrInvalidDirectiveParam, True);
          end;
        cdDefine, cdUndef: DInfo.ArgStr1 := GetIdent;
        cdIfDef, cdIfNDef:
        begin
          DInfo.ArgStr1 := GetIdent;
          FOnIfDefined(DInfo.ArgStr1, IsDefined);
          Inc(FIFCondIndex);
          FIFStateStack[FIFCondIndex] := False;
          if IsDefined xor (cdIfDef = Dir) then
          begin
            SkipTokens(DInfo);
            if not (DInfo.Directive in [cdElse, cdElseIf, cdEndIf, cdIfEnd]) then
              Error(SErrUntermCondDir, True);
            Dir := DInfo.Directive;
            goto 1;
          end
          else
            FIFStateStack[FIFCondIndex] := True;
        end;
        cdIfOpt:
        begin
          DInfo.ArgStr1 := GetIdent;
          if (Length(DInfo.ArgStr1) = 1) and (FCurLine[0] in ['+', '-']) then
          begin
            Self.FOnIfOpt(DInfo.ArgStr1[1], IsDefined);
            Inc(FIFCondIndex);
            FIFStateStack[FIFCondIndex] := False;
            if not IsDefined then
            begin
              SkipTokens(DInfo);
              if not (DInfo.Directive in [cdElse, cdElseIf, cdEndIf, cdIfEnd]) then
                Error(SErrUntermCondDir, True);
              Dir := DInfo.Directive;
              goto 1;
            end
            else
              FIFStateStack[FIFCondIndex] := True;
          end
          else
            Error(SErrInvalidDirectiveParam, True);
        end;
        cdIf:
        begin
          Self.FOnIfEval(IsDefined);
          Inc(FIFCondIndex);
          FIFStateStack[FIFCondIndex] := False;
          if not IsDefined then
          begin
            SkipTokens(DInfo);
            if not (DInfo.Directive in [cdElse, cdElseIf, cdEndIf, cdIfEnd]) then
              Error(SErrUntermCondDir, True);
            Dir := DInfo.Directive;
            goto 1;
          end
          else
            FIFStateStack[FIFCondIndex] := True;
        end;
        cdElseIf: if FIFStateStack[FIFCondIndex] or not IfEval then
          begin
            SkipTokens(DInfo);
            if not (DInfo.Directive in [cdEndIf, cdIfEnd]) then
              Error(SErrUntermCondDir, True);
            Dir := DInfo.Directive;
            goto 1;
          end
          else
            FIFStateStack[FIFCondIndex] := True;
        cdElse:
        begin
          if FIFStateStack[FIFCondIndex] then
          begin
            SkipTokens(DInfo);
            if not (DInfo.Directive in [cdEndIf, cdIfEnd]) then
              Error(SErrUntermCondDir, True);
            Dir := DInfo.Directive;
            goto 1;
          end
          else
            FIFStateStack[FIFCondIndex] := True;
        end;
        cdEndIf, cdIfEnd:
        begin
          Dec(FIFCondIndex);
        end;
        cdNoDefine, cdHPPEmit, cdExternalSym:
        begin
        end;
        cdMode:
        begin
          DInfo.ArgStr1 := GetIdent;
          if DInfo.ArgStr1 = '' then
            Error(SErrInvalidDirectiveParam, True);
        end
        else
          Assert(False);
      end;
  end;

  procedure ProcessLong(S: PAnsiChar; Len: integer; var DInfo: TDirectiveInfo); overload;
  var
    Dir: TCompilerDirective;
  begin
    if (S[0] in ['a', 'A']) and (S[1] in ['1'..'9']) then
    begin
      DInfo.Directive := cdAlign;
      if SameStr(S, Len, 'a1') then
        DInfo.ArgInt1 := 1
      else if SameStr(S, Len, 'a2') then
        DInfo.ArgInt1 := 2
      else if SameStr(S, Len, 'a4') then
        DInfo.ArgInt1 := 4
      else if SameStr(S, Len, 'a8') then
        DInfo.ArgInt1 :=
          8
      else if SameStr(S, Len, 'a16') then
        DInfo.ArgInt1 := 16
      else if SameStr(S, Len, 'a32') then
        DInfo.ArgInt1 := 32
      else
        InvalidErr(S, Len);
    end
    else if (S[0] in ['z', 'Z']) and (S[1] in ['1', '2', '4']) then
    begin
      DInfo.Directive := cdMinEnumSize;
      if SameStr(S, Len, 'z1') then
        DInfo.ArgInt1 := 1
      else if SameStr(S, Len, 'z2') then
        DInfo.ArgInt1 := 2
      else if SameStr(S, Len, 'z4') then
        DInfo.ArgInt1 := 4
      else
        InvalidErr(S, Len);
    end
    else if FindDirective(S, Len, Dir) then
      ProcessLong(Dir, DInfo)
    else
      InvalidErr(S, Len);
  end;

var
  Start: PAnsiChar;
  Len: integer;
begin
  Start := FCurLine;
  repeat
    Inc(FCurLine);
  until not (FCurLine[0] in ['A'..'Z', 'a'..'z', '0'..'9']);
  DInfo.State := False;
  DInfo.ArgStr1 := '';
  DInfo.ArgInt1 := 0;
  DInfo.ArgInt2 := 0;
  Result := False;
  Len := FCurLine - Start;
  if Len = 1 then
  begin
    case Start^ of
      'A', 'a': DInfo.Directive := cdAlign;
      'B', 'b': DInfo.Directive := cdBoolEval;
      'Q', 'q': DInfo.Directive := cdOverflowChecks;
      'U', 'u': DInfo.Directive := cdSafeDivide;
      'M', 'm': DInfo.Directive :=
          cdTypeInfo;
      'T', 't': DInfo.Directive := cdTypedAddress;
      'Z', 'z': DInfo.Directive := cdMinEnumSize;
      'J', 'j': DInfo.Directive := cdWriteableConst;
      'R', 'r': if FCurLine[0] in ['+', '-'] then
          DInfo.Directive := cdRangeChecks
        else
        begin
          ProcessResource(DInfo);
          Exit;
        end;
      'I', 'i': if FCurLine[0] in ['+', '-'] then
          DInfo.Directive := cdIOChecks
        else
        begin
          ProcessInclude(DInfo);
          Exit;
        end;
      else
        InvalidErr(Start, 1);
    end;
    if FCurLine[0] = '+' then
      DInfo.State :=
        True
    else if FCurLine[0] = '-' then
      DInfo.State := False
    else
      Error(SErrInvalidDirectiveParam, True);
    Inc(FCurLine);
    Result := FCurLine[0] = ',';
    if Result then
      Inc(FCurLine);
  end
  else
  begin
    ProcessLong(Start, Len, DInfo);
  end;
end;

function TScanner.ReadFileStr: string;

  function ReadQuotedFile: string;
  var
    Start: PChar;
    Len: integer;
  begin
    Start := FCurLine;
    repeat
      Inc(FCurLine);
    until (fCurLine[0] = #0) or (fCurLine[0] = '''');
    Len := FCurLine - Start;
    if Len > 0 then
      SetString(Result, Start, Len);
  end;

  function ReadSimpleFile: string;
  var
    Start: PChar;
    Len: integer;
  begin
    Start := FCurLine;
    repeat
      Inc(FCurLine);
      if ((FInDirective = cmsNewStyle) and (FCurLine[0] = '}')) or ((FCurLine[0] = '*') and (FCurLine[1] = ')')) then
      begin
        Dec(FCurLine);
        Break;
      end;
    until (fCurLine[0] < #32);
    Len := FCurLine - Start;
    if Len > 0 then
      SetString(Result, Start, Len);
  end;

begin
  Result := '';
  if FCurLine[0] = '''' then
    Result := ReadQuotedFile
  else
    Result := ReadSimpleFile;
end;

function TScanner.S2Bin(S: PAnsiChar; Len: integer): int64;
var
  Ok: boolean;
begin
  Result := StrP2Bin(S, Len, Ok);
  if not Ok then
    Error(SErrIntTooLarge);
end;

function TScanner.S2Hex(S: PAnsiChar; Len: integer): int64;
var
  Ok: boolean;
begin
  Result := StrP2Hex(S, Len, Ok);
  if not Ok then
    Error(SErrIntTooLarge);
end;

function TScanner.S2Int(S: PAnsiChar; Len: integer): int64;
var
  Ok: boolean;
begin
  Result := StrP2Int(S, Len, Ok);
  if not Ok then
    Error(SErrIntTooLarge);
end;

function TScanner.S2Oct(S: PAnsiChar; Len: integer): int64;
var
  Ok: boolean;
begin
  Result := StrP2Oct(S, Len, Ok);
  if not Ok then
    Error(SErrIntTooLarge);
end;

function TScanner.S2Real(S: PAnsiChar; Len: integer): double;
var
  V: extended;
  c: AnsiChar;
  Ok: boolean;
begin
  c := S[Len];
  S[Len] := #0;
  Ok := TextToFloat(S, V, fvExtended);
  S[Len] := c;
  if not Ok then
    Error(SErrInvalidRealConst);
  Result := V;
end;

procedure TScanner.SkipCurDirective;

  procedure SkipDirOldStyle;
  begin
    while (FCurLine[0] <> '*') or (FCurLine[1] <> ')') do
    begin
      if FCurLine[0] = #0 then
      begin
        if not DoFetchLine then
        begin
          Error(SErrUnexpectedEOFInComment, True);
          Exit;
        end;
      end
      else
        Inc(FCurLine);
    end;
    Inc(FCurLine, 2);
    FInDirective := cmsNone;
  end;

  procedure SkipDir;
  begin
    while FCurLine[0] <> '}' do
    begin
      if FCurLine[0] = #0 then
      begin
        if not DoFetchLine then
        begin
          Error(SErrUnexpectedEOFInComment, True);
          Exit;
        end;
      end
      else
        Inc(FCurLine);
    end;
    Inc(FCurLine);
    FInDirective := cmsNone;
  end;

begin
  if FInDirective = cmsNewStyle then
    SkipDir
  else if FInDirective = cmsOldStyle then
    SkipDirOldStyle;
end;

procedure TScanner.SkipTokens(var DInfo: TDirectiveInfo);

  procedure SkipTextToken;
  begin
    Inc(FCurLine);
    while FCurLine^ <> #0 do
    begin
      if FCurLine[0] = '''' then
      begin
        if FCurLine[1] = '''' then
          Inc(FCurLine,
            2)
        else
        begin
          Inc(FCurLine);
          Break;
        end;
      end;
      Inc(FCurLine);
    end;
  end;

  function SameStr(s1: pansichar; len1: integer; const s2: string): boolean;
  begin
    if len1 = Length(s2) then
      Result := StrLIComp(s1, pansichar(s2), len1) = 0
    else
      Result := False;
  end;

  function GetD(S: PAnsiChar; Len: integer): TCompilerDirective;
  const
    cdstrs: array[0..7] of string = ('ifdef', 'ifndef', 'if', 'ifopt', 'else', 'elseif', 'endif', 'ifend');
    cds: array[0..7] of TCompilerDirective = (cdIfDef, cdIfNDef, cdIf, cdIfOpt, cdElse, cdElseIf, cdEndIf, cdIfEnd);
  var
    i: integer;
  begin
    for i := 0 to High(cdstrs) do
      if SameStr(S, Len, cdstrs[i]) then
      begin
        Result := cds[i];
        Exit;
      end;
    Result := cdBoolEval;
  end;

  function ReadCD: TCompilerDirective;
  var
    Start: PAnsiChar;
    Len: integer;
  begin
    Start := FCurLine;
    repeat
      Inc(FCurLine);
    until not (FCurLine[0] in ['A'..'Z', 'a'..'z', '0'..'9']);
    Len := FCurLine - Start;
    Result := GetD(Start, Len);
  end;

  function GetCondD: TCompilerDirective;
  begin
    Result := cdBoolEval;
    repeat
      case FCurLine[0] of
        #0:
          if not DoFetchLine then
            Break;
        '''': SkipTextToken;
        '{': if FCurLine[1] = '$' then
          begin
            Inc(FCurLine, 2);
            Self.FInDirective := cmsNewStyle;
            Result := ReadCD;
            if Result <> cdBoolEval then
              Break;
          end
          else
          begin
            Inc(FCurLine);
            DoFetchComment;
          end;
        '(': if (FCurLine[1] = '*') and (FCurLine[2] = '$') then
          begin
            Inc(FCurLine, 3);
            Self.FInDirective := cmsOldStyle;
            Result := ReadCD;
            if Result <> cdBoolEval then
              Break;
          end
          else
          begin
            Inc(FCurLine, 2);
            DoFetchCommentOldStyle;
          end;
        else
          Inc(FCurLine);
      end;
    until False;
  end;

type
  TPPState = (ppIfEndExpect, ppEndIfExpect, ppElse);
  TPPStates = set of TPPState;
var
  D: TCompilerDirective;
  IfLevel: integer;
begin
  SkipCurDirective;
  IfLevel := 0;
  repeat
    D := GetCondD;
    case D of
      cdIfDef, cdIfNDef, cdIfOpt, cdIf:
      begin
        Inc(IfLevel);
        if IfLevel > Length(FIFStateStack) then
          Error(SErrTooManyNestedCondDir, True);
        SkipCurDirective;
      end;
      cdElse, cdElseIf: if IfLevel = 0 then
        begin
          DInfo.Directive := D;
          break;
        end;
      cdEndIf, cdIfEnd:
      begin
        DInfo.Directive := D;
        Dec(IfLevel);
        SkipCurDirective;
        if IfLevel < 0 then
          Break;
      end;
      else
        SkipCurDirective;
    end;
  until False;
end;

procedure TScanner.SkipWhiteSpace;
begin
  while FCurLine[0] in [#32, #9] do
    Inc(FCurLine);
end;

constructor TStringLineReader.Create(const S: string);
begin
  FLines := TStringList.Create;
  FLines.Text := S;
end;

destructor TStringLineReader.Destroy;
begin
  FLines.Free;
  inherited;
end;

function TStringLineReader.GetCurLine: PChar;
begin
  Result := PChar(FCurLine);
end;

function TStringLineReader.IsEOF: boolean;
begin
  Result := FEof;
end;

procedure TStringLineReader.ReadLine;
begin
  if FIndex < FLines.Count then
  begin
    FCurLine := FLines[FIndex];
    Inc(FIndex);
  end;
  if FIndex >= FLines.Count then
    FEof := True;
end;

end.
