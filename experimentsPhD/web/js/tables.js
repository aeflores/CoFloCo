

function summary_table_all(){
var table=el("table");
table.className="summary";
var line=el("tr");
line.className="trsummary";
table.appendChild(line);
var complex=["System","O(1)","O(log(n))","O(n)","O(nlog(n))","O(n^2)","O(n^3)","O(>n^3)","Infinity","No result"];
var i=0;
for( i=0;i<10;i++){
   var comp=el("td");comp.appendChild(text(complex[i]));
   line.appendChild(comp);
 }

for(i=0;i<systems.length;i++){
 table.appendChild(summary_line(systems[i]));
}
return table;
}


function loadXMLDoc(filename)
{
if (window.XMLHttpRequest)
  {
  xhttp=new XMLHttpRequest();
  }
else // code for IE5 and IE6
  {
  xhttp=new ActiveXObject("Microsoft.XMLHTTP");
  }
xhttp.open("GET",filename,false);
xhttp.send();
return xhttp.responseXML;
} 


function add_complexities(xml_elems,tag){
    var complex=[0,0,0,0,0,0,0,0,0,0];
    var name;
  for (i=0;i<xml_elems.length;i++){
      name=xml_elems[i].attributes.getNamedItem("name").nodeValue;
      //console.log(tag+name);
      complexity=xml_elems[i].getElementsByTagName(tag)[0].getElementsByTagName("complexity")[0].childNodes[0].nodeValue;
      complexity=complexity.replace(/ /g,'');
      complex[get_table_position(complexity)]++;
	   complex[9]++;
      
  }
return complex;
}


function get_table_position(complexity){
    var position;
   switch(complexity){
	       case "constant":
	       position=0;
	       break;
               case "log(n)":
	       position=1;
	       break;
	       case "n":
	       position=2;
	       break;
               case "nlog(n)":
	       position=3;
	       break;
	       case "n^2":
               position=4;
	       break;
	       case "n^3":
               position=5;
	       break;
	       case "infinity":
               position=7;
	       break;
	       case "":
                position=8;
	       break;
	       default:
                position=6;
	       }
return position;
}
function get_source_file_ref(name){
	if(name.indexOf(".c")==-1)
	  return Source_dir+name+".ces";
	else
	  return Source_dir+name;
}
function get_source_ces_file_ref(name){
	return ces_dir+name;
}
function get_complexity_number(complexity){

 switch(complexity){
	       case "O(1)":
	       return 0;
	       break;
	       case "O(n)":
               return 1;
	       break;
	       case "O(log(n))":
               return 0.5;
	       break;
	       case "O(nlog(n))":
               return 1.5;
	       break;
	       case "Inf":
	       return 100;
	       case "O()":
	          if(type_bound=="lower")
                     return 0;
                  else
	             return 100;
	       default:
               var substr=complexity.replace( /^\D+/g, '');
	       return parseInt(substr);
	       }
}

function get_entry(example,tag){
  var res=["","","",""];

  res[0]=example.getElementsByTagName(tag)[0].getElementsByTagName("result")[0].childNodes[0].nodeValue;
  if(res[0]=="inf") res="Inf";//infinity

  res[1]=example.getElementsByTagName(tag)[0].getElementsByTagName("complexity")[0].childNodes[0].nodeValue;
  res[1]=res[1].replace(/ /g,'');

 if(res[1]=="constant") res[1]="1";
 if(res[1]!="infinity") res[1]="O("+res[1]+")"; else res[1]="Inf";//infinity
 
 res[2]=example.getElementsByTagName(tag)[0].getElementsByTagName("time")[0].childNodes[0].nodeValue;

 if(example.getElementsByTagName(tag)[0].getElementsByTagName("error").length>0 &&
    example.getElementsByTagName(tag)[0].getElementsByTagName("error")[0].childNodes.length>0){
   res[3]=example.getElementsByTagName(tag)[0].getElementsByTagName("error")[0].childNodes[0].nodeValue;
 }
 return res;
}

function el(tag) {
        return document.createElement(tag);
    }
function text(t) {
        return document.createTextNode(t);
    }

function summary_line(name){
file=XMLs[name];
tag=systems_intern[name];
xmlDoc=loadXMLDoc(file);
var x=xmlDoc.getElementsByTagName("example");
var c=add_complexities(x,tag);
var line=el("tr");
line.className="trsummary";
var nametd=el("td");nametd.appendChild(text(name));
line.appendChild(nametd);
for(i=0;i<10;i++){
   var comp=el("td");comp.appendChild(text(c[i]));
   line.appendChild(comp);
 }
return line;
}
		      





function createLink(source,txt){
  var link=el("a");
  link.href=source;
  link.appendChild(text(txt));
  return link;
}
function file_column(name){
  var col=el("td");
  col.className="col1";
  col.setAttribute("rowspan","2");
  var div=el("div");
  div.className="exampleName";
  div.setAttribute("title",name);
  var sourceFile=get_source_file_ref(name);
  sourceFile=sourceFile.replace(/#/g,"%23");
  div.appendChild(createLink(sourceFile,name));
 // if(type_bound=="lower"){
 // var sourceFile_ces=get_source_ces_file_ref(name);
 // div.appendChild(createLink(sourceFile_ces," (ces_file)"));
 // }
  col.appendChild(div);

  return col;
}


 function result_column(system,name,result,type_cell){
  var source=results_dir[system]+name+out_extension[system];
  source=source.replace(/#/g,"%23");
  var col=el("td");
  switch(type_cell){
	       case "best":
                 if(type_bound=="lower")
		  col.className="col4_worst";
	         else
	          col.className="col4_best";
	       break;
          case "worst":
                 if(type_bound=="lower")
                     col.className="col4_best";
	         else
	             col.className="col4_worst";
	       break;
	       default:
	       col.className="col4";
   }

  var div=el("div");
  
  div.setAttribute("title",result);
  div.appendChild(createLink(source,result));
  col.appendChild(div);
  return col;
 }


 function extra_info_column(res){
    var col=el("td");
    col.className="complexity_td";
    var div=el("div");
    div.className="complexity_div";
    div.setAttribute("title",res[1]+"  Time:"+res[2]+" "+res[3]);
    div.appendChild(text(res[1]+" Time:" +res[2]));
    var font=el("font");
    font.color="red";font.appendChild(text(res[3]));
    div.appendChild(font);
    col.appendChild(div);
    return col;
 }


function all_results_table(){

var res=new Array();
var res_complex=new Array();
var xmls=new Array();

for(i=0;i<systems.length;i++){
    xmlDoc=loadXMLDoc(XMLs[systems[i]]);
    xmls[i]=xmlDoc.getElementsByTagName("example");
  }  

var table=el("table");
var line1=el("tr");
line1.className="trsummary";
table.appendChild(line1);

var col1=el("td");
col1.className="col1";
line1.appendChild(col1);

for(i=0;i<systems.length;i++){
 var col=el("td");
 col.className="col4";
 var div=el("div");
 div.className="title";
 div.appendChild(text(systems[i]));
 col.appendChild(div);
 line1.appendChild(col);
}


var name;
var line,line2;
for (i=0;i<xmls[0].length;i++)
  {
 name=xmls[0][i].attributes.getNamedItem("name").nodeValue;
 //console.log(name);
  line=el("tr");
  line2=el("tr");
  line.appendChild(file_column(name));
  var res_max=100;
  var index_max=-1;
  var res_min=-1;
  var index_min=-1;
  
 for(j=0;j<systems.length;j++){
   var xml=xmls[j];
   res[j]= get_entry(xml[i],systems_intern[systems[j]]);
   res_complex[j]=get_complexity_number(res[j][1]);
   if(res_complex[j]<res_max){
   	res_max=res_complex[j];
   	index_max=j;
   }else{
    if(res_complex[j]==res_max ){
      index_max=-1;
    }
   } 
   if(res_complex[j]>res_min){
   	res_min=res_complex[j];
   	index_min=j;
   }else{
    if(res_complex[j]==res_min ){
      index_min=-1;
    }
   } 
 }

    
 for(j=0;j<systems.length;j++){
 	if(index_max==j){
   line.appendChild(result_column(systems[j],name,res[j][0],"best"));
   line2.appendChild(extra_info_column(res[j]));
   }else{
   	if(index_min==j){
         line.appendChild(result_column(systems[j],name,res[j][0],"worst"));
         line2.appendChild(extra_info_column(res[j]));
      }else{
         line.appendChild(result_column(systems[j],name,res[j][0],"normal"));
         line2.appendChild(extra_info_column(res[j]));
      }
   }
   
  }
    
  table.appendChild(line);
  table.appendChild(line2);
 
}
return table;
}


function compare_table(s1,s2){


var res=new Array();
var res_complex=new Array();
var xmls=new Array();


xmlDoc=loadXMLDoc(XMLs[s1]);
xmls[s1]=xmlDoc.getElementsByTagName("example");
  
xmlDoc=loadXMLDoc(XMLs[s2]);
xmls[s2]=xmlDoc.getElementsByTagName("example");


var table=el("table");
var line1=el("tr");
line1.className="trsummary";
table.appendChild(line1);

var col1=el("td");
col1.className="col1";
line1.appendChild(col1);


 var col=el("td");
 col.className="col4";
 var div1=el("div");
 div1.className="title";
 div1.appendChild(text(s1));
 col.appendChild(div1);
 line1.appendChild(col);
 
  var col=el("td");
 col.className="col4";
 var div2=el("div");
 div2.className="title";
 div2.appendChild(text(s2));
 col.appendChild(div2);
 line1.appendChild(col);


var name;
var line,line2;
var better=0;
var worse=0;
for (i=0;i<xmls[s1].length;i++)
  {
 name=xmls[s1][i].attributes.getNamedItem("name").nodeValue;
  line=el("tr");
  line2=el("tr");
  var name_column=file_column(name);
  
 
   var xml=xmls[s1];
   res[s1]= get_entry(xml[i],systems_intern[s1]);
   res_complex[s1]=get_complexity_number(res[s1][1]);
 
   var xml=xmls[s2];
   res[s2]= get_entry(xml[i],systems_intern[s2]);
   res_complex[s2]=get_complexity_number(res[s2][1]);
   
   if (res_complex[s1]<res_complex[s2]){
     if(type_bound=="lower"){
	name_column.childNodes[0].className="exampleNameBad";
        worse++;
     }else{
      name_column.childNodes[0].className="exampleNameGood";
      better++;
     }
   }else if (res_complex[s1]>res_complex[s2]){
        if(type_bound=="lower"){
          name_column.childNodes[0].className="exampleNameGood";
          better++;
        }else{
        name_column.childNodes[0].className="exampleNameBad";
        worse++;
        }
     }
        
   
   line.appendChild(name_column);
   line.appendChild(result_column(s1,name,res[s1][0],"normal"));
   line2.appendChild(extra_info_column(res[s1]));
   line.appendChild(result_column(s2,name,res[s2][0],"normal"));
   line2.appendChild(extra_info_column(res[s2]));

  
  table.appendChild(line);
  table.appendChild(line2);
 
}
div1.appendChild(text(" has "+better+" results that are better!"));
div2.appendChild(text(" has "+worse+" results that are better!"));
return table;
}


function update_tables(){
var table_option=document.getElementsByName('table_option');

var s1_option=document.getElementsByName('system1_option');
var s2_option=document.getElementsByName('system2_option');

var title=document.getElementById('title_summary');
var summ_table=document.getElementById('summary_table');
var complete_table=document.getElementById('complete_table');

  var s1,s2;
  var table_opt;
  
      for(i = 0; i < s1_option.length; i++){
    if(s1_option[i].checked){
        s1 = s1_option[i].value;
    }}
    for(i = 0; i < s2_option.length; i++){
    if(s2_option[i].checked){
        s2 = s2_option[i].value;
    }}
      for(i = 0; i < table_option.length; i++){
    if(table_option[i].checked){
        table_opt = table_option[i].value;
    }}

       if(title.childNodes.length>0)
              title.removeChild(title.childNodes[0]);
       if(summ_table.childNodes.length>0)
              summ_table.removeChild(summ_table.childNodes[0]);
       if(complete_table.childNodes.length>0)
              complete_table.removeChild(complete_table.childNodes[0]);
      
       summ_table.appendChild(summary_table_all());
      if(table_opt=="all_systems")
            complete_table.appendChild(all_results_table());
      if(table_opt=="compare_two")
            complete_table.appendChild(compare_table(s1,s2));
  	
  	


}


window.onload = update_tables;
