//Generated by c2fsm  -cut -int
model textbook_ex4 {
var i,j,m,n;
//@parameters m,n;
states stop,start,lbl_3_14,lbl_1_17;
transition t_30 :={
  from  := start;
  to    := stop;
  guard := (1 > n);
  action:= j' = 1;
};
transition t_36 :={
  from  := start;
  to    := lbl_1_17;
  guard := ( (1 > m) && (n >= 1) );
  action:= i' = 1, j' = 2;
};
transition t_37 :={
  from  := start;
  to    := lbl_3_14;
  guard := ( (m >= 1) && (n >= 1) );
  action:= i' = 2, j' = 1;
};
transition t_32 :={
  from  := lbl_3_14;
  to    := lbl_1_17;
  guard := (i > m);
  action:= j' = j+1;
};
transition t_33 :={
  from  := lbl_3_14;
  to    := lbl_3_14;
  guard := (m >= i);
  action:= i' = i+1;
};
transition t_28 :={
  from  := lbl_1_17;
  to    := stop;
  guard := (j > n);
  action:=;
};
transition t_34 :={
  from  := lbl_1_17;
  to    := lbl_1_17;
  guard := ( (n >= j) && (1 > m) );
  action:= i' = 1, j' = j+1;
};
transition t_35 :={
  from  := lbl_1_17;
  to    := lbl_3_14;
  guard := ( (n >= j) && (m >= 1) );
  action:= i' = 2;
};
}
strategy dumb {
    Region init := { state = start && true };
}
