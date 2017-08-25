//Generated by c2fsm  -cut -int
model while2 {
var N,i,j,tmp,tmp_15;
//@parameters N;
states stop,start,lbl_2,lbl_5;
transition t_38 :={
  from  := start;
  to    := stop;
  guard := (0 >= N);
  action:= i' = N;
};
transition t_45 :={
  from  := start;
  to    := lbl_5;
  guard := (N > 0);
  action:= i' = N, j' = N-1, tmp_15' = N;
};
transition t_36 :={
  from  := lbl_2;
  to    := stop;
  guard := (0 >= i);
  action:=;
};
transition t_42 :={
  from  := lbl_2;
  to    := lbl_2;
  guard := ( (0 >= N) && (i > 0) );
  action:= i' = i-1, j' = N, tmp' = i;
};
transition t_43 :={
  from  := lbl_2;
  to    := lbl_5;
  guard := ( (N > 0) && (i > 0) );
  action:= j' = N-1, tmp_15' = N;
};
transition t_40 :={
  from  := lbl_5;
  to    := lbl_2;
  guard := (0 >= j);
  action:= i' = i-1, tmp' = i;
};
transition t_41 :={
  from  := lbl_5;
  to    := lbl_5;
  guard := (j > 0);
  action:= j' = j-1, tmp_15' = j;
};
}
strategy dumb {
    Region init := { state = start && true };
}
