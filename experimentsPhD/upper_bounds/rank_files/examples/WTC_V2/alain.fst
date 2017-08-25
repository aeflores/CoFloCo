//Generated by c2fsm  -cut -int
model alain {
var c1,c2,n1,n2,x,y,z;
//@parameters x,y;
states stop,start,stop_99,stop_100,lbl_11,lbl_14;
transition t_84 :={
  from  := start;
  to    := stop;
  guard := (2*y >= n2);
  action:= c1' = 0;
};
transition t_86 :={
  from  := start;
  to    := stop_99;
  guard := ( (y+z >= n2) && (n2 > 2*y) );
  action:= c1' = 0;
};
transition t_87 :={
  from  := start;
  to    := stop_100;
  guard := ((0 > y) ? ( (y+z >= n2) || (2*y >= n2) ) : ((0 > x) ? ( (y+z >= n2)
 || (2*y >= n2) ) : ( (y+z >= n2) || ( (2*y >= n2) || ( (n1 >= 0) && (z >= 0)
 ) ) )));
  action:= c1' = 0;
};
transition t_96 :={
  from  := start;
  to    := stop_100;
  guard := ( ( ( ( ( ( (1 > n1) && (n1 >= 0) ) && (n2 > 2*y) ) && (n2 > y+z)
 ) && (x >= 0) ) && (y >= 0) ) && (z >= 0) );
  action:= c1' = 0, n1' = n1-1;
};
transition t_98 :={
  from  := start;
  to    := lbl_14;
  guard := ( ( ( ( ( (n1 >= 1) && (n2 > 2*y) ) && (n2 > y+z) ) && (x >= 0) )
 && (y >= 0) ) && (z >= 0) );
  action:= c1' = 1, c2' = 1, n1' = n1-1, n2' = n2-1, z' = y;
};
transition t_39 :={
  from  := stop_99;
  to    := stop;
  guard := true;
  action:=;
};
transition t :={
  from  := stop_100;
  to    := stop;
  guard := true;
  action:=;
};
transition t_93 :={
  from  := lbl_11;
  to    := stop_100;
  guard := (1 > n1);
  action:= n1' = n1-1;
};
transition t_94 :={
  from  := lbl_11;
  to    := lbl_11;
  guard := ( (n1 >= 1) && (0 >= n2) );
  action:= c1' = c1+1, c2' = 0, n1' = n1-1, n2' = y+z, z' = y+z;
};
transition t_95 :={
  from  := lbl_11;
  to    := lbl_14;
  guard := ( (n1 >= 1) && (n2 > 0) );
  action:= c1' = c1+1, c2' = 1, n1' = n1-1, n2' = n2-1, z' = y;
};
transition t_89 :={
  from  := lbl_14;
  to    := lbl_11;
  guard := (0 >= n2);
  action:= n2' = y+z, z' = y+z;
};
transition t_90 :={
  from  := lbl_14;
  to    := lbl_14;
  guard := (n2 > 0);
  action:= c2' = c2+1, n2' = n2-1, z' = y;
};
}
strategy dumb {
    Region init := { state = start && true };
}
