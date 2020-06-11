(*
<test>
  <description>Check the constructor. Call Create with an instance, whether the flag is passed correctly -1</description>
  <command>%%pc %%source </command>
  <expect>
    <exitcode>0</exitcode>
    <output action="contains">IsTypePrefix=false</output>
  </expect>
</test>
*)
program ctor1;

type
	tmyobj = class
	end;

procedure test;
var
	obj: tmyobj;
begin
	obj := tmyobj(tmyobj.NewInstance);
	obj := tmyobj(obj.Create);
	obj.free;
end;

begin
	test;
end.
