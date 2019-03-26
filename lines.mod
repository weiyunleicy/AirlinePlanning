/*********************************************
 * OPL 12.6.1.0 Model
 * Author: Liming
 * Creation Date: Jun 30, 2017 at 4:55:56 PM
 *********************************************/
//create tuples*************************
tuple lsta {
   key int id;
   int ia;
   int ib;
}

tuple acstruct{
   string eq;
   int num;
}
 
tuple maxapt{
   string eq;
   int num;
}

 tuple rst {
   int ia;
   int tq;
}

tuple ods{
   string o;
   string d;
   string t;
}

//************************************	
//create sets or parameters
{rst} rsts=...;			
{lsta} las = ...;					
{int} lbs=...;
{int} lcs=...;

{acstruct} acnum=...;
{maxapt} apt_nmx=...;
{ods} odapts=...;

{int} gps=...;
{string} tms=...;
{string} apt_all=...;
{string} apt_hub=...;
{string} aptnew=...;


//{int} sa={o.ia|o in las};
{int} sb={o|o in lbs};

{int} scs=...;
float vol[las]=...;
float ama[las]=...;
float pma[las]=...;

float inc[las]=...;
float mas[las]=...;
float tsc[las]=...;
int tqe[las]=...;
string oan[las]=...;
float bcp[las]=...;

int asa[las]=...;
int asb[las]=...;

string atp[las]=...;
string lts[las]=...;

string cps[lcs]=...;
string ceq[lcs]=...;
float rtc[lcs]=...;
int flg[lcs]=...;
float mst[lcs]=...;
float fab[lcs]=...;
int dfe[lcs]=...;
int grp[lcs]=...;
string oapt[lcs]=...;
string dapt[lcs]=...;

float llcap[lcs]=...;

string flt1[lcs]=...;
string flt2[lcs]=...;
string flt3[lcs]=...;
string flt4[lcs]=...;

string typeE[lcs]=...;
string typeEM[lcs]=...;

//string dep1[lcs]=...;
//string dep2[lcs]=...;
//string arr1[lcs]=...;
//string arr2[lcs]=...;

int csa[lcs]=...;
int csb[lcs]=...;
int csc[lcs]=...;
int csd[lcs]=...;
int bsa[lbs]=...;
int bsb[lbs]=...;
float hdc[lbs]=...;
//Decision variables**************************************************
dvar boolean sel[lcs];			
dvar float+ rts[las];
dvar float+ pas[lbs];
												
//Decision expressions for objective function*************************

dexpr float trsc[i in las]=vol[i]*rts[i]*tsc[i]*1;

dexpr float hadc[i in lbs]=(pas[i])*hdc[i]*1;

dexpr float incm[i in las]=vol[i]*rts[i]*ama[i]*(inc[i]*1.2)*1000+
                                     vol[i]*rts[i]*(pma[i]-ama[i])*(inc[i])*1000+
                                             vol[i]*rts[i]*(1-pma[i])*(inc[i]*0.8)*1000;

dexpr float lamda[i in aptnew]=sum(j in lcs:matchAt(cps[j],i)>=0)sel[j];

dexpr float lload[i in lcs]=sum(j in las:csa[i]>0&&(csa[i]==asa[j]||csa[i]==asb[j]))vol[j]*rts[j]
                           +sum(j in las:csb[i]>0&&(csb[i]==asa[j]||csb[i]==asb[j]))vol[j]*rts[j]
                           +sum(j in las:csc[i]>0&&(csc[i]==asa[j]||csc[i]==asb[j]))vol[j]*rts[j]
                           +sum(j in las:csd[i]>0&&(csd[i]==asa[j]||csd[i]==asb[j]))vol[j]*rts[j];

dexpr float TotalCost=-sum(i in lcs)sel[i]*rtc[i]-sum(i in las)trsc[i]-sum(i in lbs)hadc[i]+sum(i in las) incm[i]
           /*+sum(i in las:oan[i]=="oldnew"||oan[i]=="newold"||oan[i]=="old")incm[i]*9*/
           +sum(i in lcs:mst[i]==1)lload[i]*1000*999+sum(i in aptnew)lamda[i]*999999;

//Objective function maximize minimize******************************
/*minimize TotalCost;*/ 
maximize TotalCost;

//Constraints*******************************************************
subject to {

/*MODULE1:Building business scenarios----------
************************************************/

//*The total number of the plane-------------
//-------------------------------------------			           
 forall(i in acnum)	
   ct11:
   sum(j in lcs:ceq[j]==i.eq)sel[j]>=i.num;

//*New apt limit No more than one------------
//-------------------------------------------
 forall(i in aptnew)
   ct12:
   sum(j in lcs:matchAt(flt1[j],i)==0||matchAt(flt2[j],i)==0||matchAt(flt3[j],i)==0||matchAt(flt4[j],i)==0)sel[j]<=1;	
  
//*Fleet use standard------------------------
//-------------------------------------------
 ctjudgeB733:
 forall(i in lcs:ceq[i]=="B733"&&mst[i]==0)
   lload[i]>=sel[i]*llcap[i]*0.7;
 ctjudgeB757:
 forall(i in lcs:ceq[i]=="B757"&&mst[i]==0)
   lload[i]>=sel[i]*llcap[i]*0.6; 
 ctjudgeB767:
 forall(i in lcs:ceq[i]=="B767"&&mst[i]==0)
   lload[i]>=sel[i]*llcap[i]*0.5;
   
//*Maximum take-off and landing of station----
//--------------------------------------------
 forall(i in apt_nmx:i.num<9)
   ct15:
   sum(j in lcs:matchAt(flt1[j],i.eq)==0||matchAt(flt2[j],i.eq)==0||matchAt(flt3[j],i.eq)==0||matchAt(flt4[j],i.eq)==0)sel[j]<=i.num+1;		                         		                          

//*Parking capacity---------------------------
//-------------------------------------------- 
   ctGradeC:   
   sum(j in lcs:(ceq[j]=="B733")&&flg[j]==1)sel[j]==11;
   ctGradeD:
   sum(j in lcs:(ceq[j]!="B733")&&flg[j]==1)sel[j]==13;

//*Build the hub-spoke structe:29apt-hgh------
//--------------------------------------------
 forall(i in apt_hub:i!="HAK"&&i!="TAO") //TAO and KWE dui fei hang xian
   ctHubline:
   sum(r in lcs:(matchAt(cps[r],i)==0)&&typeEM[r]=="EM")sel[r]==1;    

 forall(i in apt_hub:i!="SZX"&&i!="CAN"&&i!="PEK"&&i!="KWE"&&i!="SHE") //TAO and KWE dui fei hang xian 
   ctHublinexx:
   sum(r in lcs:(matchAt(cps[r],i)==0)&&matchAt(cps[r],"-E-")==3)sel[r]<=1; 
          
//*Must to be selected airline-----------------
//---------------------------------------------
//forall(i in lcs:(mst[i]==1&&(matchAt(cps[i],"-HGH-")>=0||matchAt(cps[i],"TPE")>=0||matchAt(cps[i],"HKG")>=0)))sel[i]==1;
 forall(i in lcs:(mst[i]==1))
   ct2x:
   sel[i]==1;

//*Transshipment Restriction-------------------
//---------------------------------------------
//ctxxx3:  
//  sum(i in las:matchAt(lts[i],"-HGH-")==5)rts[i]*vol[i]<=300;

/*END MODULE1---------------------------------- 

/*MODULE2:Abstract characteristics of business operations---
***************************************************************/

//*Time-sharing goods collection---------------
//---------------------------------------------
 forall(i in rsts)
   ct21:
   sum(j in las:j.ia==i.ia&&tqe[j]<=i.tq)rts[j]<=sum(j in las:j.ia==i.ia&&tqe[j]==i.tq)mas[j];  
    
//*Flight capacity coverage--------------------
//---------------------------------------------         	
 forall(i in scs)
   ct24:
   sum(j in lcs:i==csa[j]||i==csb[j]||i==csc[j]||i==csd[j])sel[j]*fab[j]
     ==sum(j in lbs:i==bsa[j]||i==bsb[j])(pas[j]);

//*Transport capacity limitation---------------
//---------------------------------------------        
 forall(i in sb) 							
   ct25:  
    sum(j in las:j.ib==i)rts[j]*vol[j]<=sum(j in lbs:j==i)(pas[j]);	
    	
//*Local line conflict-------------------------
//---------------------------------------------
 forall(i in gps:i>0)
   ct22:
   sum(j in lcs:i==grp[j])sel[j]<=1;
   
//*In and out of balance-----------------------
//---------------------------------------------  
 forall(i in odapts)
   ct23:
   sum(r in lcs:dfe[r]>0&&oapt[r]==i.o&&dapt[r]==i.d&&ceq[r]==i.t)sel[r]
     ==sum(r in lcs:dfe[r]>0&&dapt[r]==i.o&&oapt[r]==i.d&&ceq[r]==i.t)sel[r];
     
//*Any apt must open--------------------------- 
//---------------------------------------------
 forall(i in apt_all)
   ct26:
   sum(j in lcs:matchAt(cps[j],i)>=0)sel[j]>=1;

//*Belly Planning------------------------------
//---------------------------------------------
 forall(i in las:atp[i]=="PBM"||atp[i]=="PBL")
   ct27:
   rts[i]*vol[i]<=bcp[i];
      
//*Maximum take-off and landing of slot--------
//---------------------------------------------
// ctTotalNum:
// forall(i in tms)
//  sum(j in lcs:arr1[j]==i||arr2[j]==i||dep1[j]==i||dep2[j]==i)sel[j]<=10;
/*END MODULE2--------------------------------------
***************************************************/
}
  
// Build the tuples to show the key info
tuple result1 {
   int id;
   int blt;
}
tuple result2 {
   int id;
   float asg;
}
tuple result3 {
   int ia;
   int ib;
   float tsc;
   float rts;
}
{result1} Result1 = 
  {<i,sel[i]>|i in lcs};

{result2} Result2 = 
  {<i,pas[i]>|i in lbs};

{result3} Result3 = 
  {<i.ia,i.ib,tsc[i],rts[i]> |i in las};