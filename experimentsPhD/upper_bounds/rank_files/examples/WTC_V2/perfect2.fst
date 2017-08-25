//Generated by c2fsm  -cut -int
model perfect2 {
var x,y1,y2,y3;
//@parameters x;
states stop,start,stop_98,lbl_8,lbl_14;
transition t_76 :={
  from  := start;
  to    := stop;
  guard := (0 >= x);
  action:=;
};
transition t_94 :={
  from  := start;
  to    := stop_98;
  guard := (x = 1);
  action:= y1' = x-1, y2' = x, y3' = x;
};
transition t_95 :={
  from  := start;
  to    := lbl_14;
  guard := ( (x != 1) && (x > 0) );
  action:= y1' = x-1, y2' = 1, y3' = x;
};
transition t :={
  from  := stop_98;
  to    := stop;
  guard := true;
  action:=;
};
transition t_89 :={
  from  := lbl_8;
  to    := stop_98;
  guard := (y1 = 1);
  action:= y1' = y1-1;
};
transition t_90 :={
  from  := lbl_8;
  to    := lbl_14;
  guard := ( (y1 = 1) || (y1 > y2+1) );
  action:= y1' = y1-1, y2' = y2+1-y1;
};
transition t_91 :={
  from  := lbl_8;
  to    := lbl_8;
  guard := ( (y2 = 0) || ( (y1 = 1) || (y2+1 >= y1) ) );
  action:= y1' = y1-1, y2' = x;
};
transition t_92 :={
  from  := lbl_8;
  to    := lbl_8;
  guard := ( (y1 > y2+1) && (y2 = 0) );
  action:= y1' = y1-1, y2' = x, y3' = y3+1-y1;
};
transition t_82 :={
  from  := lbl_14;
  to    := lbl_14;
  guard := (y2 >= y1);
  action:= y2' = y2-y1;
};
transition t_83 :={
  from  := lbl_14;
  to    := lbl_8;
  guard := ( (y2 >= y1) || (y2 = 0) );
  action:= y2' = x;
};
transition t_84 :={
  from  := lbl_14;
  to    := lbl_8;
  guard := ( (y1 > y2) && (y2 = 0) );
  action:= y2' = x, y3' = y3-y1;
};
}
strategy dumb {
    Region init := { state = start && true };
}
