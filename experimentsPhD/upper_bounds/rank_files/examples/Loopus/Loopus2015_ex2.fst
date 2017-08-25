//Generated by c2fsm  -cut -int
model Loopus2015_ex2 {
var m1,m2,n,tmp,tmp_20,x,y,z;
//@parameters m1,m2,n;
states stop,start,stop_113,stop_114,lbl_20,lbl_15,stop_115;
transition t_92 :={
  from  := start;
  to    := stop;
  guard := (0 > n);
  action:= y' = n;
};
transition t_94 :={
  from  := start;
  to    := stop_113;
  guard := ( (0 > m1) && (n >= 0) );
  action:= y' = n;
};
transition t_96 :={
  from  := start;
  to    := stop_114;
  guard := ( ( (m1 >= 0) && (0 > m2) ) && (n >= 0) );
  action:= y' = n;
};
transition t_102 :={
  from  := start;
  to    := lbl_15;
  guard := ( ( (m1 >= 0) && (m2 >= 0) ) && (n > 0) );
  action:= tmp_20' = n, x' = m1+2, y' = n-1;
};
transition t_104 :={
  from  := start;
  to    := lbl_15;
  guard := ( ( (m1 >= 0) && (m2 >= 0) ) && (n > 0) );
  action:= tmp_20' = n, x' = m2+2, y' = n-1;
};
transition t_109 :={
  from  := start;
  to    := stop_115;
  guard := ( ( ( ( (0 >= m1) && (m1 >= 0) ) && (m2 >= 0) ) && (0 >= n) ) && 
(n >= 0) );
  action:= x' = m1, y' = n, z' = m1;
};
transition t_110 :={
  from  := start;
  to    := lbl_20;
  guard := ( ( ( (m1 > 0) && (m2 >= 0) ) && (0 >= n) ) && (n >= 0) );
  action:= tmp' = m1, x' = m1, y' = n, z' = m1-1;
};
transition t_111 :={
  from  := start;
  to    := stop_115;
  guard := ( ( ( ( (m1 >= 0) && (0 >= m2) ) && (m2 >= 0) ) && (0 >= n) ) && 
(n >= 0) );
  action:= x' = m2, y' = n, z' = m2;
};
transition t_112 :={
  from  := start;
  to    := lbl_20;
  guard := ( ( ( (m1 >= 0) && (m2 > 0) ) && (0 >= n) ) && (n >= 0) );
  action:= tmp' = m2, x' = m2, y' = n, z' = m2-1;
};
transition t_47 :={
  from  := stop_113;
  to    := stop;
  guard := true;
  action:=;
};
transition t_39 :={
  from  := stop_114;
  to    := stop;
  guard := true;
  action:=;
};
transition t_105 :={
  from  := lbl_20;
  to    := stop_115;
  guard := (0 >= z);
  action:=;
};
transition t_106 :={
  from  := lbl_20;
  to    := lbl_20;
  guard := (z > 0);
  action:= tmp' = z, z' = z-1;
};
transition t_100 :={
  from  := lbl_15;
  to    := lbl_15;
  guard := (y > 0);
  action:= tmp_20' = y, x' = x+2, y' = y-1;
};
transition t_107 :={
  from  := lbl_15;
  to    := stop_115;
  guard := ( (0 >= x) && (0 >= y) );
  action:= z' = x;
};
transition t_108 :={
  from  := lbl_15;
  to    := lbl_20;
  guard := ( (x > 0) && (0 >= y) );
  action:= tmp' = x, z' = x-1;
};
transition fromCut :={
  from  := stop_115;
  to    := stop;
  guard := true;
  action:=;
};
}
strategy dumb {
    Region init := { state = start && true };
}
