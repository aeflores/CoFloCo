//Generated by c2fsm  -cut -int
model counterex1c {
var b,n,tmp,tmp_37,tmp_45,x,y;
//@parameters n;
states stop,start,lbl_1,lbl_1_117,lbl_1_118,lbl_1_119;
transition t_111 :={
  from  := start;
  to    := stop;
  guard := ( ( (y > n) || (0 > x) ) || (0 > y) );
  action:=;
};
transition t_112 :={
  from  := start;
  to    := lbl_1_118;
  guard := ( ( ( (b = 0) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= b' = 1, tmp' = y, y' = y+1;
};
transition t_113 :={
  from  := start;
  to    := lbl_1;
  guard := ( ( ( (b = 0) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= tmp' = y, y' = y+1;
};
transition t_114 :={
  from  := start;
  to    := stop;
  guard := ( (0 > x) || ( (y > n) || ( (b = 0) || ( (b = 1) || (0 > y) ) ) )
 );
  action:=;
};
transition t_115 :={
  from  := start;
  to    := lbl_1_117;
  guard := ( ( ( (b = 1) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= tmp_45' = y, y' = y-1;
};
transition t_116 :={
  from  := start;
  to    := lbl_1_119;
  guard := ( ( ( (b = 1) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= b' = 0, tmp_37' = x, tmp_45' = y, x' = x-1, y' = y-1;
};
transition t_93 :={
  from  := lbl_1;
  to    := stop;
  guard := ( ( (y > n) || (0 > x) ) || (0 > y) );
  action:=;
};
transition t_94 :={
  from  := lbl_1;
  to    := lbl_1_118;
  guard := ( ( ( (b = 0) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= b' = 1, tmp' = y, y' = y+1;
};
transition t_95 :={
  from  := lbl_1;
  to    := lbl_1;
  guard := ( ( ( (b = 0) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= tmp' = y, y' = y+1;
};
transition t_96 :={
  from  := lbl_1;
  to    := stop;
  guard := ( (0 > x) || ( (y > n) || ( (b = 0) || ( (b = 1) || (0 > y) ) ) )
 );
  action:=;
};
transition t_97 :={
  from  := lbl_1;
  to    := lbl_1_117;
  guard := ( ( ( (b = 1) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= tmp_45' = y, y' = y-1;
};
transition t_98 :={
  from  := lbl_1;
  to    := lbl_1_119;
  guard := ( ( ( (b = 1) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= b' = 0, tmp_37' = x, tmp_45' = y, x' = x-1, y' = y-1;
};
transition t_105 :={
  from  := lbl_1_117;
  to    := stop;
  guard := ( ( (y > n) || (0 > x) ) || (0 > y) );
  action:=;
};
transition t_106 :={
  from  := lbl_1_117;
  to    := lbl_1_118;
  guard := ( ( ( (b = 0) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= b' = 1, tmp' = y, y' = y+1;
};
transition t_107 :={
  from  := lbl_1_117;
  to    := lbl_1;
  guard := ( ( ( (b = 0) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= tmp' = y, y' = y+1;
};
transition t_108 :={
  from  := lbl_1_117;
  to    := stop;
  guard := ( (0 > x) || ( (y > n) || ( (b = 0) || ( (b = 1) || (0 > y) ) ) )
 );
  action:=;
};
transition t_109 :={
  from  := lbl_1_117;
  to    := lbl_1_117;
  guard := ( ( ( (b = 1) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= tmp_45' = y, y' = y-1;
};
transition t_110 :={
  from  := lbl_1_117;
  to    := lbl_1_119;
  guard := ( ( ( (b = 1) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= b' = 0, tmp_37' = x, tmp_45' = y, x' = x-1, y' = y-1;
};
transition t_87 :={
  from  := lbl_1_118;
  to    := stop;
  guard := ( ( (y > n) || (0 > x) ) || (0 > y) );
  action:=;
};
transition t_88 :={
  from  := lbl_1_118;
  to    := lbl_1_118;
  guard := ( ( ( (b = 0) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= b' = 1, tmp' = y, y' = y+1;
};
transition t_89 :={
  from  := lbl_1_118;
  to    := lbl_1;
  guard := ( ( ( (b = 0) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= tmp' = y, y' = y+1;
};
transition t_90 :={
  from  := lbl_1_118;
  to    := stop;
  guard := ( (0 > x) || ( (y > n) || ( (b = 0) || ( (b = 1) || (0 > y) ) ) )
 );
  action:=;
};
transition t_91 :={
  from  := lbl_1_118;
  to    := lbl_1_117;
  guard := ( ( ( (b = 1) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= tmp_45' = y, y' = y-1;
};
transition t_92 :={
  from  := lbl_1_118;
  to    := lbl_1_119;
  guard := ( ( ( (b = 1) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= b' = 0, tmp_37' = x, tmp_45' = y, x' = x-1, y' = y-1;
};
transition t_99 :={
  from  := lbl_1_119;
  to    := stop;
  guard := ( ( (y > n) || (0 > x) ) || (0 > y) );
  action:=;
};
transition t_100 :={
  from  := lbl_1_119;
  to    := lbl_1_118;
  guard := ( ( ( (b = 0) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= b' = 1, tmp' = y, y' = y+1;
};
transition t_101 :={
  from  := lbl_1_119;
  to    := lbl_1;
  guard := ( ( ( (b = 0) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= tmp' = y, y' = y+1;
};
transition t_102 :={
  from  := lbl_1_119;
  to    := stop;
  guard := ( (0 > x) || ( (y > n) || ( (b = 0) || ( (b = 1) || (0 > y) ) ) )
 );
  action:=;
};
transition t_103 :={
  from  := lbl_1_119;
  to    := lbl_1_117;
  guard := ( ( ( (b = 1) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= tmp_45' = y, y' = y-1;
};
transition t_104 :={
  from  := lbl_1_119;
  to    := lbl_1_119;
  guard := ( ( ( (b = 1) && (n >= y) ) && (x >= 0) ) && (y >= 0) );
  action:= b' = 0, tmp_37' = x, tmp_45' = y, x' = x-1, y' = y-1;
};
}
strategy dumb {
    Region init := { state = start && true };
}
