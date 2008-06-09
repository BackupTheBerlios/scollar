%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Copyright (c) 2008 Fred Spiessens - Evoluware http://www.evoluware.eu
%%
%%
%%  -- LICENSE (MIT STYLE) --
%% Permission is hereby granted, free of charge, to any person
%% obtaining a copy of this software and associated documentation
%% files (the "Software"), to deal in the Software without
%% restriction, including without limitation the rights to use,
%% copy, modify, merge, publish, distribute, sublicense, and/or sell
%% copies of the Software, and to permit persons to whom the
%% Software is furnished to do so, subject to the following
%% conditions:
%%
%% The above copyright notice and this permission notice shall be
%% included in all copies or substantial portions of the Software.
%%
%% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
%% EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
%% OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
%% NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
%% HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
%% WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
%% FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
%% OTHER DEALINGS IN THE SOFTWARE.
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
fun{CompareStr X Y}
   XX = {List.last {String.tokens X &>}} % example X : <OPTION VALUE="caretaker.10890737">(*) caretaker
   YY = {List.last {String.tokens Y &>}}
in
   {CompareStr2 XX YY}
end

fun{CompareStr2 X Y}
   case X#Y 
   of nil#nil then true
   [] nil#(_|_) then true
   [] (_|_)#nil then false
   [] (A|T1)#(B|T2) then
      if A == B then {CompareStr2 T1 T2}
      else A < B
      end
   end
end

fun{GenerateGraph GoodSolutions Subset PredLabels Colors}
   if GoodSolutions == nil then ""
   else
      NodeIds = {Map {Record.toList GoodSolutions.1.subjects}
		     fun{$ Subj} Subj.id end}
      DW = {New DotGraph.dotGraphWrapper
	    init(nodes: NodeIds
		 edgeLabels: PredLabels
		 colors: Colors
		 getNode: fun{$ I}  node(label:GoodSolutions.1.subjects.I.name)
			  end
		 getArcs: fun{$ I J}
			     for Lbl in PredLabels Col in Colors collect:C
			     do
				Pred =	{List.toTuple Lbl [I J]}
			     in
				if  {List.all Subset
				     fun{$ Sol}
					Val = {GetPredAfterCalculation Pred Sol}
				     in
					{IsDet Val} andthen Val==1
				     end}
				then {C arc(color: Col style:solid)}
				elseif {List.some GoodSolutions
					fun{$ Sol}
					   Val = {GetPredAfterCalculation Pred Sol}
					in
					   {IsDet Val} andthen Val==1
					end}
				then {C arc(color:Col style: dashed)}
				end
			     end
			  end
		)
	   }
      %F = {VirtualString.toString '/Users/fsp/scollardata/generatedjpg/'#{RandomFileName}#'.jpg'}
      F = {Append {OS.tmpnam} ".jpg"}
   in
      {DW writeJpg(F)}
      F
   end
end

% fun{RandomFileName}
%    {VirtualString.toString 'gv_'#({OS.rand} mod 1000)#'-'#{Time.time}}
% end

fun{PredListToRows Preds Solutions} %depends on all solutions having same subjectnames!
   Unsorted = {MapInd Preds
	       fun{$ PrNr R}
		  Sz = {Width R}
	       in
		  {Flatten [{VirtualString.toString {Label R}}
			    "("
			    {Flatten {MapInd {Record.toList R}
				      fun{$ Nr Id} {Append {VirtualString.toString Solutions.1.subjectNames.Id}
						    if Sz == Nr then nil else "," end}
				      end}}
			    ")"
			    {Flatten {Map Solutions 
				      fun{$ Conf}
					 X = {GetPredAfterCalculation R Conf}
					 V =  if {IsDet X} andthen X==0 then 0 else "_" end % don't show 1's
				      in
					 {VirtualString.toString "\t"#V}
				      end}}
			    "\n"
			   ]
		  }
	       end}
in
   {Flatten
    {Sort Unsorted % we sort the whole row by 1) name of subject 2) the whole row
     fun{$ X Y} 
	T1 = {String.tokens {String.tokens X &(}.2.1 &)}.1
	T2 = {String.tokens {String.tokens Y &(}.2.1 &)}.1
	S1 = if {Member &,  T1} then {String.tokens T1 &, }.1 else T1 end
	S2 = if {Member &,  T2} then {String.tokens T2 &, }.1 else T2 end
     in
	if S1==S2 then {CompareStr2 X Y}
	else{CompareStr2 S1 S2} end
     end
    }}
end

fun{SolutionsReply TTime Nmbr GoodSolutions Completed ArcPreds Colors}
                   % ArcPreds is a set of labels of binary predicates, one color label in Colors for each label in ArcPreds
   NmbrOK = {List.length GoodSolutions}
   {ShowInfo 'found Number OK : '#NmbrOK}
   CompletedV = if Completed == true then "Search was completed in "#TTime#" seconds.\n"
		else "Search was interrupted by time out after "#TTime#" seconds.\n"
		end
   {ShowInfo CompletedV}
   NumberV = case Nmbr
	     of 0 then "Found no solutions.\n"
	     [] 1 then "Found one safe solution "#(if NmbrOK==1 then "that is also alive.\n" else "but it is not alive.\n" end)
	     else "Found "#Nmbr#" safe solutions "#(if NmbrOK==Nmbr then "that are also alive.\n"
						    elseif NmbrOK==0 then "but none of them is alive.\n"
						    elseif NmbrOK==1 then "of which one is alive.\n"
						    else "of which "#NmbrOK#" are alive.\n"end)
	     end
   {ShowInfo NumberV}
   GraphReply = {VirtualString.toString "<jpg>\n"#{GenerateGraph GoodSolutions GoodSolutions ArcPreds Colors}#"\n</jpg>\n"}
in
   {Flatten
    [ "<reply>\n"
      {VirtualString.toString CompletedV}
      {VirtualString.toString NumberV}
      GraphReply
      {SolutionsInTable GoodSolutions}
      "</reply>\n"
    ]}
   
end


fun{SolutionsInTable GoodSolutions}
   ColCount = {Length GoodSolutions}+1
   FirstRowText = {Append {Flatten {Map {List.number 0 {Length GoodSolutions} 1}
				    fun{$ Nr} if Nr == 0 then " "
					      else {VirtualString.toString "\t"#Nr}
					      end
				    end}
			  }
		   "\n"}
   RowCount
   RowsText = {SolutionsInRows GoodSolutions ?RowCount}
   Prefix = {VirtualString.toString "solutions\t"#ColCount#"\t"#RowCount#"\n"} 
in
   {Flatten ["<table>\n" % subject name, nmbr of columns, number of rows, title row excluded
	     Prefix
	     FirstRowText
	     RowsText
	     "</table>\n"]}
end

fun{SolutionsInRows GoodSolutions ?RowCount}
   AllPrevented = {Flatten {Map GoodSolutions
			    fun{$ Sol} {ToBePrevented Sol}
			    end}}
   Unique = {FoldL AllPrevented
	     fun{$ Lst X} if {Member X Lst} then Lst else X|Lst end
	     end
	     nil}
in
   RowCount = {Max {Length Unique} 1}
   if {Length Unique} > 0 then {PredListToRows Unique GoodSolutions}
   else "no restrictions necessary\t \n"
   end
end


fun{SubjectFirstRow2text Subj Conf} % subj, obj1, ... , objn    (no longer extra column for predicates with arity 1) 						    }
   {Flatten " "|{Map {Record.toList Conf.subjects}
		 fun{$ S2}
		    {VirtualString.toString "\t"#(S2.name)}
		 end}
   }
end


fun{SubjectRow2text Subj Ar Ids Conf}  % Ar is tuple access#2#k or 'may.accept'#1#b
   PredArgs={Flatten
	     {Map ((Subj.id)|Ids)
	      fun{$ I}  {Append ","{VirtualString.toString Conf.subjectNames.I}}
	      end}}.2
   %{Inspect PredArgs}
in
   if Ar.2==1
   then
      thread
	 Pred = {List.toTuple Ar.1 [Subj.id]}
	 Val =  {GetPredAfterCalculation Pred Conf}
	 Val1= {Append {PrefixForPred Pred Conf}
		if {IsDet Val} then {VirtualString.toString Val} else "_" end
	       }
      in
	 {Flatten {VirtualString.toString (Ar.1)#"("#PredArgs#")"}| %"\t"#Val1}|
	  {Map {Record.toList Conf.subjects}
	   fun{$ _} {VirtualString.toString "\t"#Val1}
	   end}}
      end
   else
      {Flatten {VirtualString.toString (Ar.1)#"("#PredArgs#",_)"}| %"\t"}|"-"|
       {MapInd {Record.toList Conf.subjects}
	fun{$ I S2}
	   thread
	      Prd = {List.toTuple Ar.1 (Subj.id)|{Append Ids [S2.id]}}
	      Val =  {GetPredAfterCalculation Prd Conf}
	   %if Prd==access(1 2) then {Wait Val} end
	      Val1 = if {IsDet Val} then {VirtualString.toString Val} else "_" end
	      %{Inspect Prd#Val#Val1}
	   in
	      {VirtualString.toString  "\t"#{PrefixForPred Prd Conf}#Val1}
	   end
	end
       }}
   end
end

fun{SubjectRow2FixptText MinSubj MaxSubj Ar Ids MinFp MaxFp}  % Ar is tuple access#2#k or 'may.accept'#1#b
   PredArgs={Flatten
	     {Map ((MinSubj.id)|Ids)
	      fun{$ I}  {Append ","{VirtualString.toString MinFp.subjectNames.I}}
	      end}}.2
   %{Inspect PredArgs}
in
   if Ar.2==1
   then
      thread
	 Pred = {List.toTuple Ar.1 [MinSubj.id]}
	 MinVal =  {GetPredAfterCalculation Pred MinFp}
	 MaxVal =  {GetPredAfterCalculation Pred MaxFp}
	 Val1= {Append {PrefixForPred Pred MinFp}
		if {IsDet MinVal}
		then if {IsDet MaxVal}
		     then if MinVal == MaxVal
			  then {VirtualString.toString MinVal}
			  else "0>1" % to become a bold "1"
			  end
		     else  "X" % should not happen
		     end
		elseif {IsDet MaxVal}
		then if MaxVal == 0 then "0"
		     elseif MaxVal == 1 then "0>1"  % to become a bold "1"
		     else "Z" % should be impossible
		     end
		else "_"
		end
	       }
      in
	 {Flatten {VirtualString.toString (Ar.1)#"("#PredArgs#")"}| %"\t"#Val1}|
	  {Map {Record.toList MinFp.subjects}
	   fun{$ _} {VirtualString.toString "\t"#Val1}
	   end}}
      end
   else
      {Flatten {VirtualString.toString (Ar.1)#"("#PredArgs#",_)"}| %"\t"}|"-"|
       {MapInd {Record.toList MinFp.subjects}
	fun{$ I S2}
	   thread
	      Prd = {List.toTuple Ar.1 (MinSubj.id)|{Append Ids [S2.id]}}
	      MinVal =  {GetPredAfterCalculation Prd MinFp}
	      MaxVal =  {GetPredAfterCalculation Prd MaxFp}
	      Val1 =  if {IsDet MinVal}
		      then if {IsDet MaxVal}
			   then if MinVal == MaxVal
				then {VirtualString.toString MinVal}
				else "0>1" % to become a bold "1"
				end
			   else  "X" % should not happen
			   end
		      elseif {IsDet MaxVal}
		      then if MaxVal == 0 then "0"
			   elseif MaxVal == 1 then "0>1"  % to become a bold "1"
			   else "Z" % should be impossible
			   end
		      else "_"
		      end
	   in
	      {VirtualString.toString  "\t"#{PrefixForPred Prd MinFp}#Val1}
	   end
	end
       }}
   end
end

fun{PrefixForPred Pred Conf}
   if {IsLivenessPred Pred Conf} then "L"
   elseif {IsSafetyPred Pred Conf} then "S"
   else ""
   end
end


fun{SubjectRows2text Subj Ar Conf}  % Ar is tuple access#2#k or 'may.accept'#1#b 
   Permuts = {Permute (Ar.2)-2 {Width Conf.subjects}}
   %{Inspect 'Permuts'#Permuts}
in
   {Flatten {Map Permuts
	     fun{$ Ids}{Append {SubjectRow2text Subj Ar Ids Conf} "\n"}
	     end}}
end

fun{SubjectRows2FixptText MinSubj MaxSubj Ar MinFp MaxFp}  % Ar is tuple access#2#k or 'may.accept'#1#b 
   Permuts = {Permute (Ar.2)-2 {Width MinFp.subjects}}
   %{Inspect 'Permuts'#Permuts}
in
   {Flatten {Map Permuts
	     fun{$ Ids}{Append {SubjectRow2FixptText MinSubj MaxSubj Ar Ids MinFp MaxFp} "\n"}
	     end}}
end

fun{SortedArities Conf} % by type, length and name
   ArsK = {Map {Sort Conf.knowledgeArities
		fun{$ A#X B#Y}
		   X < Y  orelse (X==Y
				  andthen {CompareStr {VirtualString.toString A} {VirtualString.toString B}})
		end}
	   fun{$ A#X} A#X#k end}
   ArsB = {Map {Sort Conf.behaviorArities
		fun{$ A#X B#Y}
		   X < Y  orelse (X==Y
				  andthen {CompareStr {VirtualString.toString A} {VirtualString.toString B}})
		end}
	   fun{$ A#X} A#X#b end}
in
   {Append ArsK ArsB}
end

fun{PrivateArities Subj}
   {Map {Sort Subj.locals
	 fun{$ A#X B#Y}
	    X < Y  orelse (X==Y
			   andthen {CompareStr {VirtualString.toString A} {VirtualString.toString B}})
	 end}
    fun{$ A#X} A#X#p end}
end

fun{Subject2text Subj Conf} % every subject has its own Jtable
   Ars={Append {SortedArities Conf} {PrivateArities Subj}}
   %{Inspect 'Ars'#Ars}
   FirstRowText =  {SubjectFirstRow2text Subj Conf}
   Rows = {Map Ars fun{$ A}
		      {SubjectRows2text Subj A Conf}  % A is tuple access#2#k or 'may.accept'#1#b  
		   end}
   RowsText = {Flatten Rows}
   RowCount = {Length {Filter RowsText fun{$ X} X == &\n end}}
   ColCount = {Width Conf.subjects}+1
in
   {Flatten ["<table>\n" % subject name, nmbr of columns, number of rows, title row excluded
	     {VirtualString.toString (Subj.name)#"\t"#ColCount#"\t"#RowCount#"\n"} 
	     FirstRowText
	     "\n"
	     RowsText
	     "</table>\n"]}
end

fun{Subject2FixptText SubjId MinFp MaxFp} % every subject has its own Jtable
   MinSubj = MinFp.subjects.SubjId
   MaxSubj = MaxFp.subjects.SubjId
   Ars={Append {SortedArities MinFp} {PrivateArities MinSubj}}
   FirstRowText =  {SubjectFirstRow2text MinSubj MinFp}
   Rows = {Map Ars fun{$ A}
		      {SubjectRows2FixptText MinSubj MaxSubj A MinFp MaxFp}  % A is tuple access#2#k or 'may.accept'#1#b  
		   end}
   RowsText = {Flatten Rows}
   RowCount = {Length {Filter RowsText fun{$ X} X == &\n end}}
   ColCount = {Width MinFp.subjects}+1
in
   {Flatten ["<table>\n" % subject name, nmbr of columns, number of rows, title row excluded
	     {VirtualString.toString (MinSubj.name)#"\t"#ColCount#"\t"#RowCount#"\n"} 
	     FirstRowText
	     "\n"
	     RowsText
	     "</table>\n"]}
end


fun{FixpointsReply MinFp MaxFp ArcPreds Colors}
   Tables = try  {Flatten
		  {Map {Record.toList MinFp.subjects}
		   fun{$ Subj} {Subject2FixptText Subj.id MinFp MaxFp} end}
		 }
	    catch Err then {Show Err}
	       {ErrorMsg "ERROR CONSTRUCTING FIXPOINT TABLES(Err)"}
	    end
   GraphReply = {VirtualString.toString "<jpg>\n"#{GenerateGraph [MinFp MaxFp] [MinFp MaxFp] ArcPreds Colors}#"\n</jpg>\n"}
in
   %{Inspect 'GraphReply'#{VirtualString.toAtom GraphReply}}
   {VirtualString.toString "<reply>\nCalculated Fixpoint. \n"#GraphReply#Tables#"</reply>\n"}
end

fun{ShowSolutionReply Nr Solutions ArcPreds Colors}
   Sol = {Nth Solutions Nr}
   %thread  {Inspect 'Solution nr '#Nr#' '#Sol} end
   Tables = try  {Flatten
		  {Map {Record.toList Sol.subjects}
		   fun{$ Subj} {Subject2text Subj Sol} end}
		 }
	    catch Err then {Show Err}
	       {ErrorMsg "ERROR CONSTRUCTING TABLES in ShowSolutionReply"}
	    end
   GraphReply = {VirtualString.toString "<jpg>\n"#{GenerateGraph Solutions [Sol] ArcPreds Colors}#"\n</jpg>\n"}
in
   {VirtualString.toString "<reply>\nSolution "#Nr#"\n"#GraphReply#Tables#"</reply>\n"}
end

