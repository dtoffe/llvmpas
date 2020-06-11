(*
<test>
  <description>
    getobj.docheck The getobj in this expression needs to be turned into a function call.
	(under mode delphi)
  </description>
  <command>%%pc -E %%source </command>
  <expect>
    <exitcode>0</exitcode>
  </expect>
</test>
*)
unit methptr004;

{$mode delphi}
interface

type
	tmyobj = class
	public
		procedure docheck;
	end;
	
function getobj: tmyobj;
procedure test;

implementation

function getobj: tmyobj;
begin
	result := nil;
end;

procedure test;
begin
	getobj.docheck;
end;

procedure tmyobj.docheck;
begin
end;

end.
