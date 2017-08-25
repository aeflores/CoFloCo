//Generated by c2fsm  -cut -int
model t62 {
var h,l,tmp,tmp_26;
//@parameters;
states stop,start,stop_93,lbl_4,cut,cut_43;
transition t_62 :={
  from  := start;
  to    := stop;
  guard := (l >= h);
  action:=;
};
transition t_88 :={
  from  := start;
  to    := cut;
  guard := (h > l+1);
  action:= l' = l+1, tmp_26' = l;
};
transition t_89 :={
  from  := start;
  to    := cut_43;
  guard := (h > l+2);
  action:= h' = h-1, l' = l+1, tmp' = h, tmp_26' = l;
};
transition t_90 :={
  from  := start;
  to    := stop_93;
  guard := ( (l+2 >= h) && (h > l) );
  action:= h' = h-1, l' = l+1, tmp' = h, tmp_26' = l;
};
transition t_91 :={
  from  := start;
  to    := lbl_4;
  guard := (h > l+2);
  action:= h' = h-1, l' = l+1, tmp' = h, tmp_26' = l;
};
transition t_11 :={
  from  := stop_93;
  to    := stop;
  guard := true;
  action:=;
};
transition t_84 :={
  from  := lbl_4;
  to    := cut;
  guard := (h > l+1);
  action:= l' = l+1, tmp_26' = l;
};
transition t_85 :={
  from  := lbl_4;
  to    := cut_43;
  guard := (h > l+2);
  action:= h' = h-1, l' = l+1, tmp' = h, tmp_26' = l;
};
transition t_86 :={
  from  := lbl_4;
  to    := stop_93;
  guard := (l+2 >= h);
  action:= h' = h-1, l' = l+1, tmp' = h, tmp_26' = l;
};
transition t_87 :={
  from  := lbl_4;
  to    := lbl_4;
  guard := (h > l+2);
  action:= h' = h-1, l' = l+1, tmp' = h, tmp_26' = l;
};
transition t_80 :={
  from  := cut;
  to    := cut;
  guard := (h > l+1);
  action:= l' = l+1, tmp_26' = l;
};
transition t_81 :={
  from  := cut;
  to    := cut_43;
  guard := (h > l+2);
  action:= h' = h-1, l' = l+1, tmp' = h, tmp_26' = l;
};
transition t_82 :={
  from  := cut;
  to    := stop_93;
  guard := (l+2 >= h);
  action:= h' = h-1, l' = l+1, tmp' = h, tmp_26' = l;
};
transition t_83 :={
  from  := cut;
  to    := lbl_4;
  guard := (h > l+2);
  action:= h' = h-1, l' = l+1, tmp' = h, tmp_26' = l;
};
transition t_74 :={
  from  := cut_43;
  to    := cut_43;
  guard := (h > l+1);
  action:= h' = h-1, tmp' = h;
};
transition t_75 :={
  from  := cut_43;
  to    := stop_93;
  guard := (l+1 >= h);
  action:= h' = h-1, tmp' = h;
};
transition t_76 :={
  from  := cut_43;
  to    := lbl_4;
  guard := (h > l+1);
  action:= h' = h-1, tmp' = h;
};
}
strategy dumb {
    Region init := { state = start && true };
}
