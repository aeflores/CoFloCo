//Generated by c2fsm  -cut -int
model speed_pldi09_fig4_5 {
var dir,i,m,n,tmp,tmp_15;
//@parameters dir,m,n;
states stop,start,stop_71,lbl_9,lbl_9_72,stop_73;
transition t_56 :={
  from  := start;
  to    := stop;
  guard := (0 >= m);
  action:=;
};
transition t_60 :={
  from  := start;
  to    := stop_71;
  guard := ( (m >= n) && (m > 0) );
  action:=;
};
transition t_69 :={
  from  := start;
  to    := lbl_9;
  guard := ( ( (dir = 1) && (n > m) ) && (m > 0) );
  action:= i' = m+1, tmp' = m;
};
transition t_70 :={
  from  := start;
  to    := lbl_9_72;
  guard := ( (m >= n) || ( (dir = 1) || (0 >= m) ) );
  action:= i' = m-1, tmp_15' = m;
};
transition t_27 :={
  from  := stop_71;
  to    := stop;
  guard := true;
  action:=;
};
transition t_62 :={
  from  := lbl_9;
  to    := stop_73;
  guard := ( (i >= n) || (0 >= i) );
  action:=;
};
transition t_63 :={
  from  := lbl_9;
  to    := lbl_9;
  guard := ( ( (dir = 1) && (n > i) ) && (i > 0) );
  action:= i' = i+1, tmp' = i;
};
transition t_64 :={
  from  := lbl_9;
  to    := lbl_9_72;
  guard := ( (i >= n) || ( (dir = 1) || (0 >= i) ) );
  action:= i' = i-1, tmp_15' = i;
};
transition t_65 :={
  from  := lbl_9_72;
  to    := stop_73;
  guard := ( (i >= n) || (0 >= i) );
  action:=;
};
transition t_66 :={
  from  := lbl_9_72;
  to    := lbl_9;
  guard := ( ( (dir = 1) && (n > i) ) && (i > 0) );
  action:= i' = i+1, tmp' = i;
};
transition t_67 :={
  from  := lbl_9_72;
  to    := lbl_9_72;
  guard := ( (i >= n) || ( (dir = 1) || (0 >= i) ) );
  action:= i' = i-1, tmp_15' = i;
};
transition fromCut :={
  from  := stop_73;
  to    := stop;
  guard := true;
  action:=;
};
}
strategy dumb {
    Region init := { state = start && true };
}
