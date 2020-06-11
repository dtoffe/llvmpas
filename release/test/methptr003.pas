(*
<test>
  <description>
    The expression obj.getobj in obj.getobj.docheck needs to be converted into a function call
  </description>
  <command>%%pc -E %%source </command>
  <expect>
    <exitcode>0</exitcode>
  </expect>
</test>
*)
unit methptr003;

{$mode objfpc}
interface

type
	tmyobj = class
	public
		procedure docheck;
		function getobj(): tmyobj;
	end;
	
procedure test(obj: tmyobj);

implementation

procedure test(obj: tmyobj);
begin
	obj.getobj.docheck;
end;

procedure tmyobj.docheck;
begin
end;

function tmyobj.getobj(): tmyobj;
begin
	result := Self;
end;

end.
