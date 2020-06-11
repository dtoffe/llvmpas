(*
<test>
  <description>Classes without constructors are generated and assigned to variables of the same type</description>
  <command>%%pc -E %%source </command>
  <expect>
    <exitcode>0</exitcode>
  </expect>
</test>
*)
program ctor005;
{$mode delphi}

type
	tmyobj = class
	end;

var obj: tmyobj;
begin
	obj := tmyobj.create;
	obj.free;
end.
