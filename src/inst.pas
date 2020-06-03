unit inst;

{$ifdef FPC}
{$mode delphi}
{$H+}{$J-}
{$endif}

interface

uses SysUtils, Classes, ast;

type
  TOpCode = (opcNone, opcNE, opcEQ, opcLT, opcLE, opcGT, opcGE, opcIN, opcIS, opcAS,
    opcADD, opcSUB, opcOR, opcXOR, opcMUL, opcFDIV, opcIDIV, opcMOD, opcAND, opcSHL, opcSHR,
    opcMEMBER, opcCAST, opcCALL, opcRANGE, opcINDEX, opcASSIGN, opcNOT, opcNEG, opcSET, opcADDR,
    opcINST, opcLIST, opcNIL, opcCONST, opcSymbol, opcCallSpecial, opcCallBuiltin, opcProcAddr, opcAddrOffset, opcLoad);
  TOPRAttribute = (oprConst, oprVarCast, oprVarSet, oprInherited, oprCtorInner, oprDtorInner);
  TOPRAttributes = set of TOPRAttribute;
  TCmd = class;
  TCmdList = array of TCmd;

  TNode = class
  public
    Coord: TAstNodeCoord;
    constructor Create; virtual;
  end;

  TBaseOp = class(TNode)
  private
    FCmds: TCmdList;
    FCmdCount: integer;
    FParent: TBaseOp;
    FTyp: TType;
    FOpCode: TOpCode;
  public
    Switches: TCodeSwitches;
    Attr: TOPRAttributes;
    property OpCode: TOpCode read FOpCode write FOpCode;
    property Parent: TBaseOp read FParent;
    property Typ: TType read FTyp write FTyp;
    property Cmds: TCmdList read FCmds;
    property CmdCount: integer read FCmdCount;
    procedure AddCmd(Cmd: TCmd);
    procedure Remove(Child: TBaseOp); virtual;
    procedure Detach;
    function GetReference: TSymbol;
    function GetConstantSymbol: TConstant;
    function IsTypeSymbol: boolean;
    function IsConstSymbol: boolean;
    function IsEmptyStr: boolean;
    function IsFunctionSymbol: boolean;
  end;

  TUnaryOp = class(TBaseOp)
  private
    FOperand: TBaseOp;
    procedure SetOperand(const Value: TBaseOp);
  public
    property Operand: TBaseOp read FOperand write SetOperand;
    procedure Remove(Child: TBaseOp); override;
  end;

  TBinaryOp = class(TBaseOp)
  private
    FLeft: TBaseOp;
    FRight: TBaseOp;
    procedure SetLeft(const Value: TBaseOp);
    procedure SetRight(const Value: TBaseOp);
  public
    property Left: TBaseOp read FLeft write SetLeft;
    property Right: TBaseOp read FRight write SetRight;
    procedure Remove(Child: TBaseOp); override;
  end;

  TCallKind = (callFunc, callMethod, callBuiltin, callNestFunc, callFuncPtr, callMethodPtr);
  TCallAttributes = set of (caVirtual, caClass, caSpecial);

  TCallOp = class(TBinaryOp)
  public
    SpecialVar: TVariable;
    Kind: TCallKind;
    CallAttr: TCallAttributes;
  end;

  TLoadType = (ldInt8, ldInt16, ldInt32, ldInt64, ldPtr);

  TLoadOp = class(TUnaryOp)
  public
    LoadType: TLoadType;
    Align: byte;
  end;

  TListOp = class(TBaseOp)
  public
    Items: array of TBaseOp;
    Count: integer;
    constructor Create; override;
    procedure Add(E: TBaseOp);
    procedure Insert(Index: integer; E: TBaseOp);
    procedure Delete(Index: integer);
    procedure Remove(E: TBaseOp); override;
    function IndexOf(E: TBaseOp): integer;
    procedure Replace(Index: integer; E: TBaseOp);
    procedure SetCapacity(Num: integer);
  end;

  TSymbolOp = class(TBaseOp)
  public
    Reference: TSymbol;
    Name: string;
    constructor Create; override;
  end;

  TConstOp = class(TBaseOp)
  public
    Value: TValueRec;
    constructor Create; override;
  end;

  TCmdKind = (insCall, insAssign, insSwitch, insCleanup, insHandleExcept, insHandleCtorExcept,
    insHandleScExcept, insLeaveBlock, insEndExcept, insOAInit, insInitVar, insUninitVar, insMark,
    insGoto, insJump, insRaise, insReraise, insSetMem);

  TCmd = class(TNode)
  private
    FKind: TCmdKind;
  public
    property Kind: TCmdKind read FKind;
  end;

  TCmdClass = class of TCmd;

  TCallCmd = class(TCmd)
  public
    CallOp: TBinaryOp;
    constructor Create; override;
  end;

  TAssignCmd = class(TCmd)
  public
    Left, Right: TBaseOp;
    constructor Create; override;
  end;

  TSwitchEntry = record
    Value: int64;
    Target: string;
  end;

  TSwitchEntryList = array of TSwitchEntry;

  TSwitchCmd = class(TCmd)
  private
    FEntries: TSwitchEntryList;
    FEntryCount: integer;
  public
    OtherwiseTarget: string;
    Value: TBaseOp;
    constructor Create; override;
    procedure AddEntry(Value: int64; const Target: string);
    property Entries: TSwitchEntryList read FEntries;
    property EntryCount: integer read FEntryCount;
  end;

  TJumpCmd = class(TCmd)
  public
    Condition: TBaseOp;
    TrueTarget, FalseTarget: string;
    constructor Create; override;
  end;

  TGotoCmd = class(TCmd)
  public
    Target: string;
    constructor Create; override;
  end;

  TMarkCmd = class(TCmd)
  public
    LabelName: string;
    constructor Create; override;
  end;

  TUninitVarCmd = class(TCmd)
  public
    Count: integer;
    Variables: array of TSymbol;
    constructor Create; override;
    procedure Add(V: TSymbol);
  end;

  TCleanupCmd = class(TCmd)
  public
    OutterLPad: string;
    CleanupProc: TFunction;
    constructor Create; override;
  end;

  THandleExceptCmd = class(TCmd)
  public
    OutterLPad, ExceptVar: string;
    Cmds: TFPList;
    Level: integer;
    constructor Create; override;
    destructor Destroy; override;
  end;

  THandleCtorExceptCmd = class(TCmd)
  public
    constructor Create; override;
  end;

  THandleScExceptCmd = class(TCmd)
  public
    constructor Create; override;
  end;

  TLeaveBlockCmd = class(TCmd)
  public
    constructor Create; override;
  end;

  TEndExceptCmd = class(TCmd)
  public
    ExceptVar: string;
    constructor Create; override;
  end;

  TOAInitCmd = class(TCmd)
  public
    ArrayVar: TVariable;
    Elements: array of TBaseOp;
    ElementCount: integer;
    constructor Create; override;
    procedure Add(E: TBaseOp);
  end;

  TRaiseCmd = class(TCmd)
  public
    Exception: TBaseOp;
    constructor Create; override;
  end;

  TReraiseCmd = class(TCmd)
  public
    ExceptVar: string;
    constructor Create; override;
  end;

  TSetMemCmd = class(TCmd)
  public
    Target: TBaseOp;
    Value: int64;
    Align: byte;
    constructor Create; override;
  end;

function OpMap(op: TExprOpCode): TOPCode; inline;

implementation

function OpMap(op: TExprOpCode): TOPCode;
const
  Maps: array[TExprOpCode] of TOPCode = (opcNONE, opcNE, opcEQ, opcLT, opcLE, opcGT, opcGE,
    opcIN, opcIS, opcAS, opcADD, opcSUB, opcOR, opcXOR, opcMUL, opcFDIV, opcIDIV, opcMOD, opcAND,
    opcSHL, opcSHR, opcMEMBER, opcCAST, opcCALL, opcRANGE, opcINDEX, opcASSIGN, opcNONE, opcNOT,
    opcNEG, opcNONE, opcNONE, opcSET, opcLIST, opcADDR,
    opcADDR, opcINST, opcNONE, opcNIL, opcCONST, opcSYMBOL);
begin
  Result := Maps[op];
end;

constructor TNode.Create;
begin
end;

procedure TBaseOp.AddCmd(Cmd: TCmd);
begin
  if FCmdCount >= Length(FCmds) then
    SetLength(FCmds, FCmdCount + 10);
  FCmds[FCmdCount] := Cmd;
  Inc(FCmdCount);
end;

procedure TBaseOp.Detach;
begin
  if FParent <> nil then
    FParent.Remove(Self);
end;

function TBaseOp.GetConstantSymbol: TConstant;
var
  Sym: TSymbol;
begin
  Sym := GetReference;
  if Sym.NodeKind = nkConstant then
    Result := TConstant(Sym)
  else
    Result := nil;
end;

function TBaseOp.GetReference: TSymbol;
begin
  case OpCode of
    opcSYMBOL: Result := TSymbolOp(Self).Reference;
    opcMEMBER: if TBinaryOp(Self).Right <> nil then
        Result := TBinaryOp(Self).Right.GetReference
      else
        Result := nil;
    else
      Result := nil;
  end;
end;

function TBaseOp.IsConstSymbol: boolean;
var
  Sym: TSymbol;
begin
  Sym := GetReference;
  Result := (Sym <> nil) and (Sym.NodeKind = nkConstant);
end;

function TBaseOp.IsEmptyStr: boolean;

  function IsEmptyVal(const V: TValueRec):
  boolean;
  begin
    Result := (V.VT = vtEmpty) or ((V.VT in [vtStr, vtWStr]) and (ansistring(V.VStr) = ''));
  end;

var
  Sym: TSymbol;
begin
  Result := False;
  case OpCode of
    opcSYMBOL:
    begin
      Sym := TSymbol(TSymbolOp(Self).Reference);
      if (Sym <> nil) and (Sym.NodeKind = nkConstant) then
        Result := IsEmptyVal(TConstant(Sym).Value);
    end;
    opcConst:
    begin
      Result := IsEmptyVal(TConstOp(Self).Value);
    end;
  end;
end;

function TBaseOp.IsFunctionSymbol: boolean;
var
  Sym: TSymbol;
begin
  Sym := GetReference;
  Result := (Sym <> nil) and (Sym.NodeKind in [nkFunc, nkMethod, nkExternalFunc]);
end;

function TBaseOp.IsTypeSymbol: boolean;
var
  Sym: TSymbol;
begin
  Sym := GetReference;
  Result := (Sym <> nil) and (Sym.NodeKind = nkType);
end;

procedure TBaseOp.Remove(Child: TBaseOp);
begin
end;

procedure TUnaryOp.Remove(Child: TBaseOp);
begin
  inherited;
  if FOperand = Child then
  begin
    FOperand := nil;
    Child.FParent := nil;
  end;
end;

procedure TUnaryOp.SetOperand(const Value: TBaseOp);
begin
  if FOperand = Value then
    Exit;
  if (Value <> nil) and (Value.Parent <> nil) then
    Value.Parent.Remove(Value);
  if FOperand <> nil then
    FOperand.FParent := nil;
  FOperand := Value;
  if FOperand <> nil then
    FOperand.FParent := Self;
end;

procedure TBinaryOp.Remove(Child: TBaseOp);
begin
  inherited;
  if FLeft = Child then
  begin
    FLeft := nil;
    Child.FParent := nil;
  end
  else if FRight = Child then
  begin
    FRight := nil;
    Child.FParent := nil;
  end;
end;

procedure TBinaryOp.SetLeft(const Value: TBaseOp);
begin
  if Value = FLeft then
    Exit;
  if (Value <> nil) and (Value.Parent <> nil) then
    Value.Parent.Remove(Value);
  if FLeft <> nil then
    FLeft.FParent := nil;
  FLeft := Value;
  if FLeft <> nil then
    FLeft.FParent := Self;
end;

procedure TBinaryOp.SetRight(const Value: TBaseOp);
begin
  if Value = FRight then
    Exit;
  if (Value <> nil) and (Value.Parent <> nil) then
    Value.Parent.Remove(Value);
  if FRight <> nil then
    FRight.FParent := nil;
  ;
  FRight := Value;
  if FRight <> nil then
    FRight.FParent :=
      Self;
end;

procedure TListOp.Add(E: TBaseOp);
begin
  if E.Parent = Self then
    raise EASTError.Create('expr is in use');
  if Count >= Length(Items) then
    SetLength(Items, Count + 4);
  Items
    [Count] := E;
  Inc(Count);
  if Assigned(E.Parent) then
    E.Parent.Remove(E);
  E.FParent := Self;
end;

constructor TListOp.Create;
begin
  inherited Create;
  FOpCode := opcLIST;
end;

procedure TListOp.Delete(Index: integer);
var
  i: integer;
begin
  if (Index < 0) or (Index >= Count) then
    raise EAStError.Create('Index out of bound');
  Items[Index].FParent := nil;
  for i := Index + 1 to Count - 1 do
    Items[i - 1] := Items[i];
  Dec(Count);
end;

function TListOp.IndexOf(E: TBaseOp): integer;
var
  I: integer;
begin
  for i := 0 to Self.Count - 1 do
    if Items[i] = E then
    begin
      Result := i;
      Exit;
    end;
  Result := -1;
end;

procedure TListOp.Insert(Index: integer; E: TBaseOp);
var
  i: integer;
begin
  if E.Parent = Self then
    raise EASTError.Create('expr is in use');
  if (Index < 0) or (Index > Count) then
    raise EASTError.Create('Index out of bound');
  if Count >= Length(Items) then
    SetLength(Items, Count + 4);
  Inc(Count);
  for i := Index + 1 to Count - 1 do
    Items[i] := Items[i - 1];
  Items[Index] := E;
  if E.Parent <> nil then
    E.Parent.Remove(
      E);
  E.FParent := Self;
end;

procedure TListOp.Remove(E: TBaseOp);
var
  i: integer;
begin
  inherited
  Remove(E);
  for i := 0 to Self.Count - 1 do
    if Items[i] = E then
    begin
      Delete(i);
      Exit;
    end;
end;

procedure TListOp.Replace(Index: integer; E: TBaseOp);
begin
  if (Index < 0) or (Index >= Count) then
    raise EASTError.Create('Index out of bound');
  Items[Index].FParent := nil;
  Items[Index] := E;
  if E.Parent <> nil then
    E.Parent.Remove(E);
  E.FParent := Self;
end;

procedure TListOp.SetCapacity(Num: integer);
begin
  if Num < Count then
    Exit;
  SetLength(Items, Num);
end;

constructor TSymbolOp.Create;
begin
  inherited;
  FOpCode := opcSYMBOL;
end;

constructor TConstOp.Create;
begin
  inherited;
  FOpCode := opcCONST;
end;

constructor TCallCmd.Create;
begin
  inherited;
  FKind := insCall;
end;

constructor TAssignCmd.Create;
begin
  inherited;
  FKind := insAssign;
end;

procedure TSwitchCmd.AddEntry(Value: int64; const Target: string);
begin
  if FEntryCount >= Length(FEntries) then
    SetLength(FEntries, FEntryCount + 10);
  FEntries
    [FEntryCount].Value := Value;
  FEntries[FEntryCount].Target := Target;
  Inc(FEntryCount);
end;

constructor TSwitchCmd.Create;
begin
  inherited;
  FKind := insSwitch;
end;

constructor TJumpCmd.Create;
begin
  inherited;
  FKind := insJump;
end;

constructor TGotoCmd.Create;
begin
  inherited;
  FKind := insGoto;
end;

constructor TMarkCmd.Create;
begin
  inherited;
  FKind := insMark;
end;

constructor TCleanupCmd.Create;
begin
  inherited Create;
  FKind := insCleanup;
end;

constructor THandleExceptCmd.Create;
begin
  inherited Create;
  FKind := insHandleExcept;
  Cmds := TFPList.Create;
end;

destructor THandleExceptCmd.Destroy;
begin
  Cmds.Free;
  inherited
  Destroy;
end;

constructor THandleCtorExceptCmd.Create;
begin
  inherited;
  FKind := insHandleCtorExcept;
end;

constructor THandleScExceptCmd.Create;
begin
  inherited;
  FKind := insHandleScExcept;
end;

constructor TLeaveBlockCmd.Create;
begin
  inherited;
  FKind := insLeaveBlock;
end;

constructor TEndExceptCmd.Create;
begin
  inherited;
  FKind := insEndExcept;
end;

procedure TOAInitCmd.Add(E: TBaseOp);
begin
  if ElementCount = Length(Elements) then
    SetLength(Elements, ElementCount + 10);
  Elements[ElementCount] := E;
  Inc(ElementCount);
end;

constructor TOAInitCmd.Create;
begin
  inherited Create;
  FKind := insOAInit;
end;

procedure TUninitVarCmd.Add(V: TSymbol);
begin
  if Count = Length(Variables) then
    SetLength(Variables, Count + 4);
  Variables[Count] := V;
  Inc(Count);
end;

constructor TUninitVarCmd.Create;
begin
  inherited Create;
  FKind := insUninitVar;
end;

constructor TReraiseCmd.Create;
begin
  inherited Create;
  FKind := insReraise;
end;

constructor TRaiseCmd.Create;
begin
  inherited Create;
  FKind := insRaise;
end;

constructor TSetMemCmd.Create;
begin
  inherited Create;
  FKind := insSetMem;
end;

end.
