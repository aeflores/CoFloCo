//Generated by c2fsm  -cut -int
model t11 {
var m,n,x,y;
//@parameters m,n;
states stop,start,lbl_1,lbl_1_35;
transition t_32 :={
  from  := start;
  to    := stop;
  guard := (x >= n);
  action:=;
};
transition t_33 :={
  from  := start;
  to    := lbl_1;
  guard := ( (m > y) && (n > x) );
  action:= y' = y+1;
};
transition t_34 :={
  from  := start;
  to    := lbl_1_35;
  guard := ( (y >= m) && (n > x) );
  action:= x' = x+1;
};
transition t_26 :={
  from  := lbl_1;
  to    := stop;
  guard := (x >= n);
  action:=;
};
transition t_27 :={
  from  := lbl_1;
  to    := lbl_1;
  guard := ( (m > y) && (n > x) );
  action:= y' = y+1;
};
transition t_28 :={
  from  := lbl_1;
  to    := lbl_1_35;
  guard := ( (y >= m) && (n > x) );
  action:= x' = x+1;
};
transition t_29 :={
  from  := lbl_1_35;
  to    := stop;
  guard := (x >= n);
  action:=;
};
transition t_30 :={
  from  := lbl_1_35;
  to    := lbl_1;
  guard := ( (m > y) && (n > x) );
  action:= y' = y+1;
};
transition t_31 :={
  from  := lbl_1_35;
  to    := lbl_1_35;
  guard := ( (y >= m) && (n > x) );
  action:= x' = x+1;
};
}
strategy dumb {
    Region init := { state = start && true };
}
