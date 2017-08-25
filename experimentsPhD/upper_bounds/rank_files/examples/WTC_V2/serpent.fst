//Generated by c2fsm  -cut -int
model serpent {
var n,x,y;
//@parameters n;
states stop,start,W2,W1,lbl_7,stop_73;
transition t_53 :={
  from  := start;
  to    := stop;
  guard := (0 >= n);
  action:=;
};
transition t_70 :={
  from  := start;
  to    := W1;
  guard := (n > 0);
  action:= x' = n, y' = n-1;
};
transition t_71 :={
  from  := start;
  to    := lbl_7;
  guard := (n > 0);
  action:= x' = n-1, y' = n;
};
transition t_72 :={
  from  := start;
  to    := W2;
  guard := (n > 0);
  action:= x' = n-1, y' = n+1;
};
transition t_59 :={
  from  := W2;
  to    := lbl_7;
  guard := true;
  action:=;
};
transition t_60 :={
  from  := W2;
  to    := W2;
  guard := (n >= y);
  action:= y' = y+1;
};
transition t_56 :={
  from  := W1;
  to    := W1;
  guard := (y >= 0);
  action:= y' = y-1;
};
transition t_61 :={
  from  := W1;
  to    := lbl_7;
  guard := true;
  action:= x' = x-1;
};
transition t_62 :={
  from  := W1;
  to    := W2;
  guard := (n >= y);
  action:= x' = x-1, y' = y+1;
};
transition t_65 :={
  from  := lbl_7;
  to    := stop_73;
  guard := (0 > x);
  action:=;
};
transition t_66 :={
  from  := lbl_7;
  to    := W1;
  guard := ( (x >= 0) && (y >= 0) );
  action:= y' = y-1;
};
transition t_67 :={
  from  := lbl_7;
  to    := lbl_7;
  guard := (x >= 0);
  action:= x' = x-1;
};
transition t_68 :={
  from  := lbl_7;
  to    := W2;
  guard := ( (n >= y) && (x >= 0) );
  action:= x' = x-1, y' = y+1;
};
transition fromCut_37 :={
  from  := stop_73;
  to    := stop;
  guard := true;
  action:=;
};
}
strategy dumb {
    Region init := { state = start && true };
}
