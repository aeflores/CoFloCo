//Generated by c2fsm  -cut -int
model random2d {
var N,i,r,x,y;
//@parameters N;
states stop,start,lbl_5,lbl_5_113,lbl_5_114,lbl_5_115,lbl_5_116,lbl_8_49;
transition t_111 :={
  from  := start;
  to    := stop;
  guard := (0 >= N);
  action:= i' = 0, x' = 0, y' = 0;
};
transition t_112 :={
  from  := start;
  to    := lbl_8_49;
  guard := (N > 0);
  action:= i' = 1, r' = ?, x' = 0, y' = 0;
};
transition t_109 :={
  from  := lbl_5;
  to    := stop;
  guard := (i >= N);
  action:=;
};
transition t_110 :={
  from  := lbl_5;
  to    := lbl_8_49;
  guard := (N > i);
  action:= i' = i+1, r' = ?;
};
transition t_99 :={
  from  := lbl_5_113;
  to    := stop;
  guard := (i >= N);
  action:=;
};
transition t_100 :={
  from  := lbl_5_113;
  to    := lbl_8_49;
  guard := (N > i);
  action:= i' = i+1, r' = ?;
};
transition t_101 :={
  from  := lbl_5_114;
  to    := stop;
  guard := (i >= N);
  action:=;
};
transition t_102 :={
  from  := lbl_5_114;
  to    := lbl_8_49;
  guard := (N > i);
  action:= i' = i+1, r' = ?;
};
transition t_103 :={
  from  := lbl_5_115;
  to    := stop;
  guard := (i >= N);
  action:=;
};
transition t_104 :={
  from  := lbl_5_115;
  to    := lbl_8_49;
  guard := (N > i);
  action:= i' = i+1, r' = ?;
};
transition t_105 :={
  from  := lbl_5_116;
  to    := stop;
  guard := (i >= N);
  action:=;
};
transition t_106 :={
  from  := lbl_5_116;
  to    := lbl_8_49;
  guard := (N > i);
  action:= i' = i+1, r' = ?;
};
transition t_93 :={
  from  := lbl_8_49;
  to    := lbl_5;
  guard := ( (r > 3) || (0 > r) );
  action:=;
};
transition t_94 :={
  from  := lbl_8_49;
  to    := lbl_5_113;
  guard := (r = 0);
  action:= x' = x+1;
};
transition t_95 :={
  from  := lbl_8_49;
  to    := lbl_5_114;
  guard := (r = 1);
  action:= x' = x-1;
};
transition t_96 :={
  from  := lbl_8_49;
  to    := lbl_5_115;
  guard := (r = 2);
  action:= y' = y+1;
};
transition t_97 :={
  from  := lbl_8_49;
  to    := lbl_5_116;
  guard := (r = 3);
  action:= y' = y-1;
};
}
strategy dumb {
    Region init := { state = start && true };
}
