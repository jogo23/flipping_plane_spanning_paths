PROGRAM CheckPathFlipGraphConnectivity;

{ License: CC-BY }

{ Check for all order types of fixed cardinality if the graph of all plane spanning path is connected by simple edge flips of Type 1 }

{ For n=10, execution on a standard computer (if not parallelized) takes roughly 20 CPU years }

{ Adapt the first 3 constants below and then compile with fpc (free pascal compiler). Besides the file containing the order types no other source files are needed }

{ Adapt the following constant and names for different number of points (here n=10); For n<=8 the input files are named otypes0X.b08 }
CONST  n = 10; { Fix the cardinality of the point set / order type. }
   infilename	 = 'otypes10.b16'; { Name of input file with all order types; Available at www.ist.tugraz.at/staff/aichholzer/research/rp/triangulations/ordertypes/data/otypes10.b16 }
   exceptionname = 'exceptions10.b16'; {File to store order types which are counterexamples, if any exist }   
   maxpath	 = 552000; {Max. number of path; good for n<=10}

{ Adapt the coordinate type for n <= 8 }
TYPE coordtype = word; { Change to byte for input file with n<=8 }
     pathtype    = ARRAY[1..n] OF byte;

{----------------------------------------------------------------------}

TYPE point = RECORD x,y:coordtype END;

VAR  infile, exceptionfile : FILE of coordtype;     
     isleft   : ARRAY[1..n,1..n,1..n] OF boolean; {Contains the orientation of every labeled point triple }
     pointset : ARRAY [1..n] OF point; {point set considered }
     anzpath  : longint; { Number of plane spanning path of this set }
     pmerk    : ARRAY [1..maxpath] OF pathtype; { Stores all theese plane spanning path }
     nr	      : LongInt;  { Number of input set in the order type file (needed only in case of a counterexample to identify the point set) }
{----------------------------------------------------------------------}

FUNCTION SKALARPROD(pi,pj,pq:point):comp;
{ Compute the scalar product of the three points to determine their orientation }
VAR pix,piy,pjx,pjy,pqx,pqy:comp;
BEGIN
  pix:=pi.x;
  piy:=pi.y;
  pjx:=pj.x;
  pjy:=pj.y;
  pqx:=pq.x;
  pqy:=pq.y;
  skalarprod := piy*pqx-pjy*pqx+pjy*pix
               +pjx*pqy-pix*pqy-pjx*piy;
END;

{----------------------------------------------------------------------}
PROCEDURE WRITEEXCEPTION;
{ Output the couterexample, if one is found }
VAR i : integer;
BEGIN
   FOR i:=1 TO n DO
      write(exceptionfile,pointset[i].x,pointset[i].y);
END;
{----------------------------------------------------------------------}

PROCEDURE NEXTSET;
{ Read the next set from the input order type file, compute orientations for all point triples }

VAR i,j,k  : integer;
    links  : boolean;

BEGIN
  {$I-}
   FOR i:=1 TO n DO
      read(infile,pointset[i].x,pointset[i].y);     
   IF IOResult<>0 THEN BEGIN
      writeln('ERROR: reading file');
      HALT;
   END;
  {$I+}
   
  FOR i:=1 TO n DO
    FOR j:=i+1 TO n DO
      FOR k:=j+1 TO n DO BEGIN
        links:=(skalarprod(pointset[i],pointset[j],pointset[k]) > 0);
        isleft[i,j,k]:=links;
        isleft[j,k,i]:=links;
        isleft[k,i,j]:=links;
        isleft[j,i,k]:=NOT links;
        isleft[i,k,j]:=NOT links;
        isleft[k,j,i]:=NOT links;
      END;
END;

{----------------------------------------------------------------------}

FUNCTION INTERSECT(i,j,k,l:integer):boolean;
{ Compute if two segments intersect, using the orientation of the involved point triples }
BEGIN
  intersect := (isleft[i,j,k]<>isleft[i,j,l]) AND (isleft[k,l,i]<>isleft[k,l,j]);
END;

{----------------------------------------------------------------------}

PROCEDURE GENERATE_PATH;
{ Generate all plane spanning path of the given point set by recursively adding a (potential) furhter point and checking for planarity }
{ Count the number of generated path and store them all for later use }

TYPE point_degree = ARRAY[1..n] OF integer; 
     edge_ok	  = ARRAY[1..n,1..n] OF BOOLEAN;
   
VAR p			 : pathtype;  
    used		 : ARRAY[1..n] OF boolean;
    i,j			 : integer;
   startpoint,largerleft : integer;
   init_pd		 : point_degree;
   init_edge_ok		 : edge_ok;
   

PROCEDURE ADD_POINT(indx : integer; nr:integer; pd:point_degree; eo:edge_ok);

VAR x,y : integer;
    ok  : boolean;

BEGIN
   p[indx]:=nr;
   used[nr]:=TRUE;
   IF nr>startpoint THEN DEC(largerleft);
   IF indx=n THEN BEGIN
      INC(anzpath);
      pmerk[anzpath]:=p;
   END ELSE IF largerleft>0 THEN BEGIN
      ok:=TRUE;
      
      FOR x:=1 TO p[indx-1]-1 DO IF NOT used[x] THEN IF eo[x,p[indx-1]] THEN
	 IF eo[x,p[indx-1]] THEN BEGIN
	    eo[x,p[indx-1]]:=FALSE;
            DEC(pd[x]);
            IF pd[x]=0 THEN ok:=FALSE;
	 END;
      FOR x:=p[indx-1]+1 TO n DO IF NOT used[x] THEN IF eo[p[indx-1],x] THEN
	 IF eo[p[indx-1],x] THEN BEGIN
	    eo[p[indx-1],x]:=FALSE;
	    DEC(pd[x]);
	    IF pd[x]=0 THEN ok:=FALSE;
	 END;
      
      FOR x:=1 TO n DO IF NOT used[x] THEN
	 FOR y:=x+1 TO n DO IF NOT used[y] THEN IF eo[x,y] THEN
	    IF intersect(x,y,p[indx-1],p[indx]) THEN BEGIN
	       eo[x,y]:=FALSE;
	       
	       DEC(pd[x]); IF pd[x]=0 THEN ok:=FALSE;
	       DEC(pd[y]); IF pd[y]=0 THEN ok:=FALSE;

	    END;
      IF ok THEN FOR x:=1 TO p[indx]-1 DO IF (NOT used[x]) AND eo[x,p[indx]] THEN
	 add_point(indx+1,x,pd,eo);
      IF ok THEN FOR x:=p[indx]+1 TO n DO IF (NOT used[x]) AND eo[p[indx],x] THEN
	 add_point(indx+1,x,pd,eo);
   END;
   IF nr>startpoint THEN INC(largerleft);
   used[nr]:=FALSE;
END;

BEGIN
   anzpath:=0;
   FOR i:=1 TO n DO BEGIN
      init_pd[i]:=n-1;
      used[i]:=FALSE;
      FOR j:=i+1 TO n DO
	 init_edge_ok[i,j]:=TRUE;
   END;
   
   FOR startpoint:=1 TO n-1 DO BEGIN
      p[1]:=startpoint;
      used[startpoint]:=TRUE;
      largerleft:=n-startpoint;
      FOR j:=1 TO n DO IF j<>startpoint THEN
         add_point(2,j,init_pd,init_edge_ok);
      used[startpoint]:=FALSE;
   END;
END;

{----------------------------------------------------------------------}
{----------------------------------------------------------------------}


PROCEDURE TRYFLIPPING;
{ Starting with the first plane spanning path make all legal flips; For each 'new' path that is generated in this proceess we add it to the list of paths we have to check }
{ If the number of path is the same as generated before, the flip graph is connected and we stop for that point set; If we get less paths, we found a counter example }

VAR status : ARRAY[1..maxpath] OF byte;
   i,indx,anzfound   : LongInt;

   FUNCTION SMALLER(p1,p2 : pathtype; VAR gl:boolean):boolean;
   { Path p1 is smaller than path p2 iff the first index of a point that differes is smaller for p1 than for p2 (lexicographic order) }
   VAR k : integer;
   BEGIN
      gl:=FALSE;
      smaller:=FALSE;
      FOR k:=1 TO n DO
	 IF p1[k]<>p2[k] THEN BEGIN
	    smaller:=(p1[k]<p2[k]);
	    EXIT;
	 END;
      gl:=TRUE;
   END;

   PROCEDURE INVERT(VAR p : pathtype; a,b:integer);
   { Invert order of path so that first point always has a smaller index than the last point }
   VAR k : integer;
      p2 : pathtype;
   BEGIN
      p2:=p;
      FOR k:=a TO b DO
	 p[k]:=p2[a+b-k];
   END;

   PROCEDURE FOUNDPATH(p :pathtype);
   { If a flip is legal we found a path and can add the corresponding edge in the flip graph }
   VAR a,b,k : LongInt;
      identical : boolean;
   BEGIN
      IF p[1]>p[n] THEN
	 invert(p,1,n);
      a:=1;
      b:=anzpath;
      REPEAT
	 k:=(a+b) DIV 2;
	 IF smaller(p,pmerk[k],identical) THEN
	    b:=k-1
	 ELSE
	    a:=k+1;
      UNTIL identical OR (a>b);
      IF NOT identical THEN BEGIN
	 writeln('Error: Path search error (which should be impossible)');
	 writeln(a,' - ',k,' - ',b);
         FOR k:=1 TO n DO
	    write(p[k],' ');
	 writeln;
	 HALT;
      END;
      
      IF status[k]=0 THEN BEGIN
	 status[k]:=1;
	 IF k<indx THEN indx:=k;
	 INC(anzfound);
      END;
   END;

   FUNCTION NUMBEROFCROSSINGS(p	:pathtype;  a,b : integer):integer;
   { test the edge of the path spanned by the indices a b for crossings with the other edges of the path p}
   VAR k,cr : integer;
   BEGIN
      cr:=0;
      FOR k:=1 TO n-1 DO
	 IF (a<>k) AND (b<>k) AND (a<>(k+1)) AND (b<>(k+1)) THEN
	    IF intersect(p[k],p[k+1],p[a],p[b]) THEN
	       INC(cr);
      numberofcrossings:=cr;
   END;

   PROCEDURE FLIP(k : LongInt);
   { Make all legal flips in path number k }
   VAR a,b : integer;
      p1,p2     : pathtype;
   BEGIN
      p1:=pmerk[k];
	  {Flip around the first point}
      a:=1;
      FOR b:=3 TO n DO
	 IF numberofcrossings(p1,a,b)=0 THEN BEGIN
	    p2:=p1;
	    invert(p2,1,b-1);
	    foundpath(p2);
	 END;
	 {Flip around last point}
      b:=n;
      FOR a:=1 TO n-2 DO
	 IF numberofcrossings(p1,a,b)=0 THEN BEGIN
	    p2:=p1;
	    invert(p2,a+1,n);
	    foundpath(p2);
	 END;
      a:=1;
      b:=n;
   END;

	    

   
BEGIN
   status[1]:=1;
   FOR i:=2 TO anzpath DO
      status[i]:=0;
   anzfound:=1;
   indx:=1;
   WHILE (anzfound<anzpath) AND (indx<=anzpath) DO BEGIN
      WHILE (indx <= anzpath) AND (status[indx]<>1) DO
	 INC(indx);
      IF indx<=anzpath THEN BEGIN
	 status[indx]:=2;
	 flip(indx);
      END;
   END;
   IF anzfound=anzpath THEN
      writeln('Flip Graph connected!')
   ELSE BEGIN
      writeexception;
      writeln('========================================================');
      writeln('Flip Graph NOT connected!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!');
      writeln('========================================================');
   END;
END;

{----------------------------------------------------------------------}
{----------------------------------------------------------------------}


BEGIN {main}
   { Main Loop over all order types in the input file }
   assign(infile,infilename);
   RESET(infile);
   assign(exceptionfile,exceptionname);
   rewrite(exceptionfile);
   nr:=0;
   WHILE NOT EOF(infile) DO BEGIN
      nextset;
      INC(nr);
      generate_path;
      writeln(nr,': number of path: ',anzpath);
	  tryflipping;
   END;
   CLOSE(infile);
   CLOSE(exceptionfile);
END.  {main}
