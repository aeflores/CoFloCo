//Generated by c2fsm  -cut -int
model jama_ex4 {
var a,b,c,d,i,j,tmp,tmp_20;
//@parameters a,b,c,d;
states stop,start,lbl_2_10,lbl_1_23;
transition t_38 :={
  from  := start;
  to    := stop;
  guard := (a > b);
  action:= i' = a;
};
transition t_44 :={
  from  := start;
  to    := lbl_2_10;
  guard := ( (b >= a) && (d >= c) );
  action:= i' = a, j' = c+1, tmp' = c;
};
transition t_45 :={
  from  := start;
  to    := lbl_1_23;
  guard := ( (b >= a) && (c > d) );
  action:= i' = a+1, j' = c, tmp_20' = a;
};
transition t_40 :={
  from  := lbl_2_10;
  to    := lbl_2_10;
  guard := (d >= j);
  action:= j' = j+1, tmp' = j;
};
transition t_41 :={
  from  := lbl_2_10;
  to    := lbl_1_23;
  guard := (j > d);
  action:= i' = i+1, tmp_20' = i;
};
transition t_36 :={
  from  := lbl_1_23;
  to    := stop;
  guard := (i > b);
  action:=;
};
transition t_42 :={
  from  := lbl_1_23;
  to    := lbl_2_10;
  guard := ( (b >= i) && (d >= c) );
  action:= j' = c+1, tmp' = c;
};
transition t_43 :={
  from  := lbl_1_23;
  to    := lbl_1_23;
  guard := ( (b >= i) && (c > d) );
  action:= i' = i+1, j' = c, tmp_20' = i;
};
}
strategy dumb {
    Region init := { state = start && true };
}
