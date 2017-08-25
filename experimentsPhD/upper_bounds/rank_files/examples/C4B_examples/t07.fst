//Generated by c2fsm  -cut -int
model t07 {
var x,y;
//@parameters;
states stop,start,lbl_7,lbl_1;
transition t_36 :={
  from  := start;
  to    := lbl_1;
  guard := (x > 0);
  action:= x' = x-1, y' = y+2;
};
transition t_47 :={
  from  := start;
  to    := lbl_7;
  guard := ( (0 >= x) && (y > 0) );
  action:= y' = y-1;
};
transition t_48 :={
  from  := start;
  to    := stop;
  guard := ( (0 >= x) && (0 >= y) );
  action:=;
};
transition t_41 :={
  from  := lbl_7;
  to    := lbl_7;
  guard := (y > 0);
  action:= y' = y-1;
};
transition t_42 :={
  from  := lbl_7;
  to    := stop;
  guard := (0 >= y);
  action:=;
};
transition t_34 :={
  from  := lbl_1;
  to    := lbl_1;
  guard := (x > 0);
  action:= x' = x-1, y' = y+2;
};
transition t_44 :={
  from  := lbl_1;
  to    := lbl_7;
  guard := ( (0 >= x) && (y > 0) );
  action:= y' = y-1;
};
transition t_45 :={
  from  := lbl_1;
  to    := stop;
  guard := ( (0 >= x) && (0 >= y) );
  action:=;
};
}
strategy dumb {
    Region init := { state = start && true };
}
