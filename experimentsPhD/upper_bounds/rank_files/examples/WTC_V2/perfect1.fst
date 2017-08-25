//Generated by c2fsm  -cut -int
model perfect1 {
var tmp,x,y1,y2,y3;
//@parameters x;
states stop,start,stop_86,lbl_10,lbl_8_28;
transition t_69 :={
  from  := start;
  to    := stop;
  guard := (1 >= x);
  action:=;
};
transition t_83 :={
  from  := start;
  to    := lbl_10;
  guard := (x > 1);
  action:= y1' = x-1, y2' = 1, y3' = x;
};
transition t :={
  from  := stop_86;
  to    := stop;
  guard := true;
  action:=;
};
transition t_77 :={
  from  := lbl_10;
  to    := lbl_10;
  guard := (y2 >= y1);
  action:= y2' = y2-y1;
};
transition t_78 :={
  from  := lbl_10;
  to    := lbl_8_28;
  guard := ( (y2 >= y1) || (y2 = 0) );
  action:= tmp' = y1, y1' = y1-1, y2' = x;
};
transition t_79 :={
  from  := lbl_10;
  to    := lbl_8_28;
  guard := ( (y1 > y2) && (y2 = 0) );
  action:= tmp' = y1, y1' = y1-1, y2' = x, y3' = y3-y1;
};
transition t_73 :={
  from  := lbl_8_28;
  to    := stop_86;
  guard := (0 >= y1);
  action:=;
};
transition t_80 :={
  from  := lbl_8_28;
  to    := lbl_10;
  guard := ( (y2 >= y1) && (y1 > 0) );
  action:= y2' = y2-y1;
};
transition t_81 :={
  from  := lbl_8_28;
  to    := lbl_8_28;
  guard := ( (0 >= y1) || ( (y2 >= y1) || (y2 = 0) ) );
  action:= tmp' = y1, y1' = y1-1, y2' = x;
};
transition t_82 :={
  from  := lbl_8_28;
  to    := lbl_8_28;
  guard := ( (y1 > 0) && (y2 = 0) );
  action:= tmp' = y1, y1' = y1-1, y2' = x, y3' = y3-y1;
};
}
strategy dumb {
    Region init := { state = start && true };
}
