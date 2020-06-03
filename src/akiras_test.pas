program Test;

type
  TTestRec = record    
    IntField: LongInt;
  end;
  
  PTestRec = ^TTestRec;
  
  function MakeRecord(const IL: LongInt): PTestRec;
  begin
    Result := nil;
    GetMem(Result, SizeOf(TTestRec));
    Result^.IntField := IL;
  end;

  function Test(const P: PLongInt; const Count: LongInt): LongInt;
  var I, J: LongInt;
  begin
	  Result := 0;
	  for I := 0 to Pred(Count) do
		  Result := Result + P[I];
	  J := 2;
	  Inc(Result, J);
  end;

var 
  I: LongInt;
  Z: array[0..4] of LongInt;
  Ptr: PTestRec = nil;

begin
  for I := 0 to 4 do
    Z[I] := I;
  Ptr := MakeRecord(Test(@Z[0], 5));
  with PTR^ do
  begin
    IntField := 1;
    IntField := 2;
    IntField := 3;
    IntField := 4;
    IntField := 5;
  end;
  FreeMem(Ptr);
end.