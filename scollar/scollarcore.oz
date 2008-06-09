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
%% ADDED (AND FIXED) EXISTENTIAL QUANTIFICATION
%% ADDED AGGREGATION
%% REMOVED UNUSED KNOWLEDGE PREDICATES IN PREPARATION FOR EXCHANGE
%% ADDED EXCHANGE
%% REPLACED BYNEED RELEVANCE BY EXPLICIT RELEVANCE
%% MADE THINGS DETERMINISTIC (seems to make it almost twice as slow though!)
%% REFACTORED GETPRED
%% STARTING FROM PARSETREE AND LOOKING ONLY FOR PROOF OF SAFETY VIOLATION
%% SYSTEM RULES ARE EXPLICIT
%% DETECTS REAL LIVENESS AFTER SEARCH
%% FIXED BUG THAT CAUSED BLOCKING OR FAILURE WHEN KNOWLEGE PREDICATES WERE NOT IN ANY E HEAD
%% FIXING BUG THAT CAUSED QUERY SUBJECT PREDICATES TO BE CLOSED UNDER SUBJECTS RULES
%% ADDED fixpoint calculation
%% ...should we not learn MORE from non-live solutions.
%% Config can contain and group query predicates too :  ?access(a b) ....
%% => the fixpoint will ignore them, the "solutions" will search for the maximum sets
%% SUBJECTS CAN HAVE DEFAULT BEHAVIOR, CALLED 'DEFAULT', if 'DEFAULT' IS UNSPECIFIED, IT IS {}
%% => now BEHAVIOR can be empty
%% INTEROPERATION: REMOVED
%% 
%% IN PROGRESS (from core_04.oz on):
%% - REDUCING DATASTRUCTURE OVERHEAD;
%% - - what is 1 in minimal fixpt is always 1 (already works like this from first step)
%% - - what is not 1 in maximal fixpt is always 0 (NO NEED TO MAKE SAFETY PROPERTIES OF IT)
%% - - only the rest has to be searched for, and copied.
%% - - the datastructure should be bare bones!
%%
%%
%% adding restart 
%%declare
Me = {NewName}

MapInd = List.mapInd

proc{GetSystemArities Problem  Conf}
   Conf.behaviorLabels = {Map Problem.'declare'.behavior fun{$ Decl} Decl.label end}
   Conf.knowledgeLabels = {Map {Append Problem.'declare'.permission
				Problem.'declare'.knowledge}
			   fun{$ Decl} Decl.label end}
   Conf.behaviorArities = {Map Problem.'declare'.behavior fun{$ Decl} (Decl.label)#(Decl.arity) end}
   Conf.knowledgeArities =  {Map {Append Problem.'declare'.permission
				  Problem.'declare'.knowledge}
			     fun{$ Decl} (Decl.label)#(Decl.arity) end}
end

proc{LazyTuple Size Dim Pred ByNeedAction TplOrV} % assert Dim>=0, Size>1, ByNeedAction is lazy
   TplOrV =  {ByNeed                                       % call for every PredLabel of every subject to build structure lazily
	      fun{$}
		 %{Show 'inLazyTuple'(pred:Pred dim:Dim size:Size)}
		 if Dim == 0
		 then {ByNeedAction Pred} % by need because we may make a whole tuple of which only one value is needed
		 else TplOrV =  {MakeTuple '#' Size} % will fail if structure shortcut is used, so use structure shortcut only
		    {Record.forAllInd TplOrV         %   at highest level (Subj.label), only when no rules are instantiated  
		     proc{$ I Y}
			{LazyTuple Size Dim-1
			 {Record.adjoinAt Pred {Width Pred}+1 I}
			 ByNeedAction
			 Y}
		     end}
		    TplOrV
		 end
	      end}
end


% predicates stuff -----------------
   
fun{GetPred Pred Conf }
   Feat = {Label Pred}
   Subj = Conf.subjects.(Pred.1) 
in
   if {HasFeature Subj Feat}
   then        % will make structure needed but should not block
      thread {GetPredValue Subj.Feat {Record.toList Pred}.2} end  
   else 0      
   end
end

fun{GetPredValue Val Keys}     % make structure needed to cause structure being build where necessary             
   case Keys                   % may block and cause structure to be built
   of nil then Val             % will not make retreived variable needed
   [] Key|T then               % can be used to retreive variable corresponding to partial structure (shorten Keys)
      if {IsInt Val} then Val  % make needed and stop when shortcut structure is detected
      else
	 {GetPredValue Val.Key T}
      end
   end
end

proc{TellPred Prd Conf Val}  % will not block, may cause structure to be built,
   Val = {GetPred Prd Conf}      % may cause rules to be installed (not when both sides are undetermined)
end                          % may cause faulure 

fun{IsEvenOneInMinFixpt Pred Conf} % TODO: OPTIMIZE
   {Member Pred Conf.minFixptOnePreds}
end

fun{IsEvenZeroInMaxFixpt Pred Conf} % TODO : OPTIMIZE
   {Member Pred Conf.maxFixptZeroPreds} 
end

fun{IsRelevantForDistributionPred Pred Conf}  % ASK ONLY FOR QUERY PREDICATES THAT NEED DISTRIBUTING PLEASE!!!   
   Feat = {Label Pred}                        % will block for structure to be build but not cause the building
   Subj = Conf.subjects.(Pred.1)              % will not make value needed
in
   if {IsDet Subj.Feat} andthen {IsNumber Subj.Feat} then false
   elseif {Not {IsNeeded Subj.Feat}} then false
   else
      Nmbr#Needed#_ = {FoldL {Record.toList Pred}.2
		       fun{$ Nr#Ndd#V K} if Nr orelse {Not Ndd} then Nr#Ndd#V % don't go deeper
					 else  ({IsDet V.K} andthen {IsNumber V.K})#{IsNeeded V.K}#(V.K)
					 end
		       end
		       ({IsDet Subj.Feat} andthen {IsNumber Subj.Feat})#{IsNeeded Subj.Feat}#(Subj.Feat)}
   in
      {Not Nmbr} andthen Needed
   end
end

%----   
fun{IsDetPred Pred Conf} % for globals!  Makes nothing needed    
% used : 1) to sort predicates in rule body (not just qpreds) => undeterministic and therefore may invalidate use of recalculation strategy
%        2) to filter solution predicates (not only qpreds) upon success, when space is stable => deterministic
   Feat = {Label Pred}
   Subj = Conf.subjects.(Pred.1)
in                                          
   if {Not {HasFeature Subj Feat}} then true  % always zero! TODO: double check that all query predicates get at least feature structure
   elseif {IsDet Subj.Feat} andthen {IsInt Subj.Feat} then true
   else
      {IsDetPredValue Subj.Feat {Record.toList Pred}.2}
   end
end
fun{IsDetPredValue Val Keys}   % DOES NOT make structure needed             
   case Keys                   % NEVER blocks 
   of nil then {IsDet Val}     % IS UTTERLY UNDETERMINISTIC    
   [] Key|T then              
      {IsDet Val} andthen ({IsInt Val} orelse  {IsDetPredValue Val.Key T}) 
   end
end
%----  
proc{MakeLabelNeeded Subj Lbl Ar Conf}
   %{Show 'in MakeLabelNeeded'(subjId: Subj.id lbl:Lbl ar:Ar confSize: Conf.size)}
   %{Show 'hasFeature'(subjId: Subj.id trueOrFalse:{HasFeature Subj Lbl})}
   if {Not {HasFeature Subj Lbl}} then skip  % always zero! TODO: double check that all query predicates get at least feature structure
   elseif {IsDet Subj.Lbl} andthen {IsInt Subj.Lbl} then skip
   else
      {MakePredsNeeded Subj.Lbl Ar-1 Conf.size} 
   end
   %{ShowInfo 'done MakeLabelNeeded'}
end
proc{MakePredsNeeded Val Depth Size}
   %{ShowInfo 'in MakePredsNeeded'}
   {Value.makeNeeded Val} % cause structure to become needed
   if Depth == 0  then skip  
   elseif {IsDet Val} andthen {IsInt Val} then skip
   else
      thread %  wait for structure in separate thread
	 if {IsInt Val} then skip
	 else for I in 1 .. Size do
		 {MakePredsNeeded Val.I Depth-1 Size}
	      end
	   end
      end
   end
  % {ShowInfo 'done MakePredsNeeded'}
end
%----  
proc{ForAllSubjectLabels Conf P4} % P4/4 will be called : {P Subj.id Lbl LblArity Conf}
   {Record.forAll Conf.subjects
    proc{$ Subj}
       {ForAll {GetAllSubjectPredLabels Subj}
	proc{$ Lbl}
	   Ar =  {LabelArity Subj.id Lbl Conf}
	in
	   {P4 Subj Lbl Ar Conf}
	end}
    end}   
end
%----
fun{IsDetPredAndEquals Pred V Conf}   % Asked only after MakeComplete was called on Conf. Structure should be complete by now
   Feat = {Label Pred}
   Subj = Conf.subjects.(Pred.1)
in                                          
   if {Not {HasFeature Subj Feat}} then V == 0  % TODO: double check that all query predicates get at least feature structure
   elseif {IsDet Subj.Feat} andthen Subj.Feat == V then true
   else
      {IsDetPredValueAndEquals Subj.Feat {Record.toList Pred}.2 V}
   end
end
fun{IsDetPredValueAndEquals Val Keys V}   % DOES NOT make structure needed             
   case Keys                   
   of nil then
      {IsDet Val} andthen Val == V       
   [] Key|T then              
      {IsDet Val} andthen (Val==V orelse ({Not {IsInt Val}} andthen {IsDetPredValueAndEquals Val.Key T V})) 
   end
end
fun{DeterminedZeroPreds Conf} % call only after calling MakeComplete to make sure nothing extra is made needed
   {Filter {GetAllPreds Conf}
    fun{$ Pred} {IsDetPredAndEquals Pred 0 Conf} 
    end}
end
fun{DeterminedOnePreds Conf} % call only after calling MakeComplete to make sure nothing extra is made needed
   {Filter {GetAllPreds Conf}
    fun{$ Pred} {IsDetPredAndEquals Pred 1 Conf}
    end}
end
%----
fun{GetPredAfterCalculation Pred Conf } % assume calculation is completely finished
   Feat = {Label Pred}
   Subj = Conf.subjects.(Pred.1) 
in
   if {HasFeature Subj Feat}
   then        % will NOT  make structure needed 
      {GetPredValueAfterCalculation Subj.Feat {Record.toList Pred}.2}
   else 0      
   end
end
fun{GetPredValueAfterCalculation Val Keys} % will NOT make structure needed
   if {Not {IsDet Val}} then Val
   else
      case Keys                   
      of nil then Val             
      [] Key|T then
	 if {IsInt Val} then Val
	 else
	    {GetPredValueAfterCalculation Val.Key T}
	 end
      end
   end
end
%----
fun{GetAllPreds Conf}
   {Flatten
    {Map {Record.toList Conf.subjects}
     fun{$ Subj}
	{Flatten {Map {GetAllSubjectPredLabels Subj}
		  fun{$ Lbl}
		     {AllPredPermutations Subj.id Lbl {LabelArity Subj.id Lbl Conf} Conf.size}
		  end}}
      end}}
end

%--- SORTING THE PREDICATES TO MINIMIZE UNNECCESSARY SEARCH AND RULE INSTANCE MUTLIPLICATION

fun{MultipleIndex Pred Maxm ?NmbrOfMultiplications} % TODO : CHECK AND TEST ALTENATIVES
   %ASSUMING Max >= {Width Pred}
   Index     %eg: Max==3 Pred==iEmit(2 y 4) => Index = 0b1010 (first 1 from Max, second 1 from y not being integer)
             %eg: Max==3 Pred==access(2 4)  => Index = 0b1000 (last 0 is from Max being >= {Width Pred})
             %NmbrOfMultiplications is the number of DIFFERENT atoms (non-integers) in the predicate
in
   NmbrOfMultiplications#Index#_
   = {List.foldLInd {Append {Record.toList Pred} {List.number 1 Maxm-{Width Pred} 1}}
                % appending dummy numbers to generate extra zeros at the end
      fun{$ I Nmbr#Ix#Atoms Arg}
	 if {IsInt Arg} then Nmbr#Ix#Atoms
	 elseif {Member Arg Atoms} then Nmbr#(Ix+{Pow 2 (Maxm-I)})#Atoms
	 else (Nmbr+1)#(Ix+{Pow 2 (Maxm-I)})#(Arg|Atoms)
	 end
      end
      0#({Pow 2 Maxm})#nil
     }
   Index   
end

fun{ConditionPriorityCompare Pred1 Pred2}  % boolean indicating if Pred1 should be evaluated before Pred2
   L1 = {Width Pred1}                      % both preds are not-yet-defined (or they were a split second ago)
   L2 = {Width Pred2}                      % 
   L = {Value.max L1 L2}
   M1 M2  % to contain number of predicate instantiations needed
   I1 = {MultipleIndex Pred1 L M1}  % the lower, the more the multiplications are towards the end
   I2 = {MultipleIndex Pred2 L M2}
in
   (M1<M2 orelse (M1==M2 andthen (I1<I2 orelse (I1==I2 andthen L1=<L2))))
end

fun{PartialSorted Preds Conf}
    % ORDER IS INDETERMINISTICCALLY DEFINED => MAY PREVENT USE OF RECALCULATION DISTANCE 
    % for sorting predicates in body of a rule with an instantiated head
    % test the instantiated and determined predicates first, then sort by less need (and then less early need) for instantiation of the body of the rule
   DetPreds UndetPreds
in
   {List.partition Preds fun{$ Prd}
			    {Record.all Prd IsInt} % already instantiated
			    andthen {IsDetPred Prd Conf} % also already defined
			 end
    DetPreds
    UndetPreds}
   {Append DetPreds {Sort UndetPreds ConditionPriorityCompare}}
end

% rule instantiation stuff -------------------------

% We defer existential quantification until it is needed for the first Pred !
proc{TestConditions RawPreds Vars Conf RuleHeadValue} % RuleHeadValue is 0#1 FD variable
   % for optimisation: sort so that first the predicates that have less non-instantiated arguments or not-yet-determined values are tested
   % due to recursion, sort is re-executed for every predicate and then in every existential quantification step
   Preds = {PartialSorted RawPreds Conf}  
in
   case Preds
   of Prd|T then
      NextVar = {Record.foldL Prd    % find the first non-integer field in the first condition predicate 
		 fun{$ I Fld} if {IsInt I}
			      then Fld
			      else I
			      end
		 end
		 0}
   in
      if {IsInt NextVar}  % all features in Prd are integers => no more variables left in Prd
      then
	 thread  
	    case T of nil
	    then RuleHeadValue = {GetPred Prd Conf} 
	    else 
	       ThisVal = {GetPred Prd Conf}
	    in
	       if ThisVal == 0
	       then RuleHeadValue=0   % conjunction , no need to continue
	       else {TestConditions T Vars Conf RuleHeadValue}
	       end
	    end
	 end
      else % existential quantification in Prd : instantiate NextVar once for every subject
           % ignore zero's except the last one
	 PartialValues = {FD.tuple '#' Conf.size 0#1}
	 Alternatives = {Map {List.number 1 Conf.size 1}
			 fun{$ I}  %instantiate NextVar in Vars
			    ExtVars = {Record.adjoinAt Vars NextVar I}
			 in
			     % replace NextVar by I in all Preds
			    {Map Preds
			     fun{$ C} {Record.map C
				       fun{$ V} if {IsInt V} then V else ExtVars.V end end}
			     end}
			    #ExtVars#I
			 end}
      in
	 {FD.sum PartialValues '>=:' RuleHeadValue} % close world
	 {List.forAll Alternatives proc{$ ExtC#ExtV#J} % disjunction
				    %thread 
			            % try
				      RuleHeadValue >=: PartialValues.J
				      {TestConditions ExtC ExtV Conf PartialValues.J}
		                    % catch _ then Value.failed  % TODO: find out in what cases we fail here and what to do then
			            %end 
				end}
      end
   [] nil then RuleHeadValue = 1 % for body-less rules
   end
end

proc{Instantiate Rule Head Conf RuleHeadValue} % Head and all preds in Rule are global!!
                                              % Head is COMPLETELY instantiated clone of Rule.head !!
   % trying to allow implicit unification of parameters with same name in head is TOO LATE HERE !!
   % TODO : check what the above means and clarify
   Vars =  {Record.clone Rule.vars}  %Rule.vars is something like vars(x:x y:y z:z) for behavior rules and
                                     % vars(x:_ y:_ z:_) for system rules
                                     % TODO: this has changed. System rules should now also have vars like vars(x:x y:y z:z)
   Body = {Map Rule.body 
	   fun{$ ConditionPred} {Record.map ConditionPred fun{$ Atm} Vars.Atm end} end}
   % now the fresh Body-to-be-instantiated contains fresh variables corresponding to those in the Rule.vars clone Vars
   Failed
in
   try
      Head = {Record.map Rule.head fun{$ Atm} Vars.Atm end} % unifying vars with corresponding variables in Head
            % now the body is maximally instantiated with subject ids from the head
            % BUT IF Rule.head CONTAINS TWICE THE SAME VARIABLE, THIS CAUSES FAILURE OF THE SPACE
            % INSTEAD IT SHOULD JUST CAUSE THE RULE TO FAIL DUE TO A BROKEN IMPLICIT EQUALITY CONDITION!
      Failed = false
   catch Err then % WHAT ERROR SHOULD WE ACTUALLY CATCH ?
      {ShowInfo "Failed Head unification in rule -->"}
      {Show Err}
      {ShowInfo "<-- Failed Head unification in rule"}
      Failed = true
   end 
   if Failed then
      RuleHeadValue = 0
   else
      {Record.forAllInd Vars proc{$ Atm V}
				if {Not {IsDet V}} % assigns feature atom to all non-instantiated vars in body 
				then V=Atm         % e.g. vars(x:1 y:_ z:3) becomes vars(x:1 y:y z:3)
				end
			     end}
      % because of the unification, a body pred might now look like : 'did.getfromfor'(x 1 y 2) but also : 'did.getfromfor'(x 1 x 1) 
      {TestConditions Body Vars Conf RuleHeadValue}
   end
end

proc{InstantiateDisjunction Rules Head Conf CloseWorld PredValue}
   % Head and all preds in Rule are global!!
   % Head.1 is subject's ID, and all other fields are instantiated too.
   % Rules can be nil
   % Head can be wrongly specified for some of the Rules e.g. 'did.get'(1 2 3) for ...=>'did.get'(A A B)
   % We take care of that first
   RelevantRules = {Filter Rules fun{$ R} {TemplateMatchesInstance R.head Head} end} 
   RuleResults =  {FD.tuple '#' {Length RelevantRules} 0#1}  % RuleResults = '#' when RelevantRules == nil
in
   {List.forAllInd RelevantRules proc{$ I R} 
				    {Instantiate R Head Conf RuleResults.I}
				    PredValue >=: RuleResults.I
				 end}
   if CloseWorld then
      {FD.sum RuleResults '>=:' PredValue}  % works perfect even in case RuleResults=='#' => PredValue=0
   end
end

proc{InstantiateWhenNeeded SubjId Lbl Rules Conf}
  % Rules can be nil now
  % all rules are global and have same head (modulo names of parameters)!!
   Args = {LabelArity SubjId Lbl Conf}-1
in
   Conf.subjects.SubjId.Lbl
   = {LazyTuple Conf.size Args
      {Record.adjoinAt Lbl 1 SubjId} % seed for Lazytyple: eg. access(SubjId) to be completed to access(SubjId 1) etc
      proc{$ Pred ?Val}  % Pred is global and will be completely instantiated by LazyTuple by the time it gets used!!
	 {ByNeed fun{$}  
		    Val={FD.int 0#1} 
		    if {IsInitFact Pred Conf}
		    then        % don't instantiate rules, not necessary
		       Val = 1  % OK for query predicates too
		    elseif {IsEvenOneInMinFixpt Pred Conf}  % 
		    then        % don't instantiate rules, not necessary
		       Val = 1  % OK for query predicates too
		    elseif {IsEvenZeroInMaxFixpt Pred Conf}
		    then        % don't instantiate rules, not necessary
		       Val = 0  % OK for query predicates too.
		    elseif {IsQueryPred Pred Conf}
		    then        % do not close world, e.g. if Rules==nil then Val remains unchanged
		       Val = {InstantiateDisjunction Rules Pred Conf false} 
		    else        % close world, e.g. if Rules==nil then Val=0
		       Val = {InstantiateDisjunction Rules Pred Conf true} 
		    end
		    Val
		 end
	  Val}
      end
     }
end


proc {InstallRules Subj Conf} % will close the world by using disjunctive conditions, except when deriving query predicates
                              % detects always derived and never derived properties (the latter except for query predicates)
   AllRules = {Append Conf.system Subj.rules} % could contain duplicates
   BodylessRules = {Filter AllRules fun{$ R} R.body==nil end} % could contain duplicates
   SubjectLabels = {GetAllSubjectPredLabels Subj} % all predicate labels that can have Subj as first argument
   SubjectNonQueryNorInitLabels = {GetSubjectNonQueryNorInitLabels Subj Conf} % all labels (including system behavior !) that are not in subject's query predicates or init predicates
   HeadLabels = {Filter SubjectLabels
		 fun{$ Lbl} {List.some AllRules fun{$ R} {Record.label R.head}==Lbl
						end}
		 end}
   AlwaysLabels = {Filter HeadLabels
		   fun{$ Lbl}
		      {List.some BodylessRules
		       fun{$ R} {Record.label R.head}==Lbl
			  andthen {Not {ImplicitUnificationInRuleHead R.head}} % e.g. not for access(x x)
		       end}
		   end}
   %{Inspect 'AlwaysLabels'#AlwaysLabels}
   NeverLabels = {Filter  % don't touch query predicates or init predicates
		  SubjectNonQueryNorInitLabels
		  fun{$ Lbl} {Not {Member Lbl HeadLabels}} 
		  end}
   %{Inspect 'NeverLabels'#NeverLabels}
   Extremes = {Append AlwaysLabels NeverLabels}
   NonExtremes = {Filter SubjectLabels fun{$ Lbl}
					  {Not {Member Lbl Extremes}}
				       end}
in
   %{ShowInfo '-> will set neverLabels to 0'}
   for Lbl in NeverLabels do Subj.Lbl = 0 end % OK even for fixpoints
   %{ShowInfo '-> will set AlwaysLabels to 1'}
   for Lbl in AlwaysLabels do
      Subj.Lbl = 1
   end
   %{ShowInfo '-> will instantiate NonExtremes when necessary'}
   for Lbl in NonExtremes do                    % we call InstantiateWhenNeeded for every Label here because
      {InstantiateWhenNeeded Subj.id Lbl           % it should lazily build the structue
       {Filter AllRules fun{$ R} R.body \= nill andthen {Label R.head} == Lbl
			end}  % can result in nil : for query predicates with no (bodyless) rules
       Conf}
   end
   %{ShowInfo '-> done instantiating NonExtremes when necessary'}
end

fun{TemplateMatchesInstance TemplPred InstPred}
   % e.g. TemplPred = 'did.get'(<N:Me> x  x)  InstPred = 'did.get'(1 1 1)  => true
   % e.g. TemplPred = 'did.get'(<N:Me> x  x)  InstPred = 'did.get'(2 2 4)  => false
   % simply try unification
   if {Width TemplPred} \= {Width InstPred} 
   then raise unexpectedWidthDifferencesInTemplateMatchesInstance end % this should not happen !
      false
   elseif  {Label TemplPred} \= {Label InstPred}
   then raise unexpectedLabelDifferencesInTemplateMatchesInstance end % this should not happen !
      false
   else
      try
	 TestRec = {ExtractFeatures testrec {Record.toList TemplPred}}  % e.g. : testrec(<N:Me>:_ x:_)
      in
	 {Record.forAllInd TemplPred proc{$ Index Key}
					TestRec.Key = InstPred.Index
				     end}
	 true
      catch _ then false
      end
   end
end

%------------------------ configuration parsing -------------------------

fun{ExtractFeatures Rec Lst}  % returns Record with unique features in Lst and undefined fields
   case Lst of H|T
   then {ExtractFeatures {Record.adjoinAt Rec H _} T}
   [] nil then Rec
   end
end

fun{GlobalRuleToGlobal GR}  % give system rule its variables structure (fresh field variables)
                            % GR should have only one pred in head   
   Rule = {Record.adjoinAt GR vars {ExtractFeatures vars {Flatten {Record.toList GR.head}|
						   {Map GR.body fun{$ C} {Record.toList C} end}}}}
   {Record.forAllInd Rule.vars proc{$ I V} V=I end}  % TODO: this is new, to be similar to LocalRuleToGlobal. Is it OK?
in
   Rule
end

fun{LocalRuleToGlobal LR}  % turn local behavior rule into global and give it its variables structure
                           % then set the variable fields to the features
                           % LR should have only one pred in head
   Rule =  rule(head: {LocalPredToGlobal LR.head}
		body: {Map LR.body LocalPredToGlobal}
		vars: {ExtractFeatures vars Me|{Flatten {Record.toList LR.head}|
						{Map LR.body fun{$ C} {Record.toList C} end}}})
   {Record.forAllInd Rule.vars proc{$ I V} V=I end}
in
   Rule
end

fun{LocalPredToGlobal Pred}
   {List.toTuple {Label Pred} Me|{Record.toList Pred}}
end

fun{IsLivenessPred Pred Conf}
   {Member Pred Conf.liveness} 
end

fun{IsSafetyPred Pred Conf}
   {Member Pred Conf.safety}
end

fun{GetQPredsFromQSIds Conf} % don't add the ones that can be determined to be 1 from static analysis of the query subject's minimal behavior
   {FoldR Conf.qsIds
    fun{$ Id Lst}
       {FoldR Conf.behaviorArities
	fun{$ Lbl#Ar Lst1}
% 	   if {IsAlwaysTrueBehaviorQueryPredLabel Conf.subjects.Id Lbl}
% 	   then Lst1
% 	   else
	   {FoldR {Permute Ar-1 Conf.size}
	    fun{$ Perm Lst2}
	       {List.toTuple Lbl Id|Perm}|Lst2
	    end
	    Lst1}
% 	   end
	end
	Lst}
    end
    nil}
end

fun{ParseConfig Problem}
   %if Options.debug then {Show inParseConfig} end
   AllSubjects = {List.toRecord '#' {Map Problem.subject fun{$ S} (S.name)#S end}}
   Conf = {NewConf {Width AllSubjects}}
   {GetSystemArities Problem Conf}
   SysRules = {Map Problem.system GlobalRuleToGlobal}
   NameToSubjId = {List.toRecord '#'  {MapInd Problem.subject fun{$ I S} (S.name)#I end}}
   SubjIdToName =  {List.toRecord '#' {MapInd Problem.subject fun{$ I S} I#(S.name) end}}
   fun{NamedPredToId Pred}
      {Record.map Pred fun{$ Nm} NameToSubjId.Nm end}
   end
   fun{GetRulesFor Subj} 
      Problem.behavior.(Subj.type).rules
   end
   fun {BuildSubject Id}
      Nm = SubjIdToName.Id
      S = AllSubjects.Nm
      LocalRules = {GetRulesFor S}
      SubjRules = {Map LocalRules LocalRuleToGlobal}
      SubjInit = {Map {Filter Problem.config.facts
		       fun{$ Fact} Fact.1 == S.name end}
		  fun{$ Prd}
		     {NamedPredToId Prd}
		  end}
      SubjFeatures = {Flatten
		      [[name id rules locals type init]
		       Conf.knowledgeLabels
		       %(if S.search then Conf.behaviorLabels 
			%else nil end)
		       Conf.behaviorLabels
		       {Record.arity Problem.behavior.(S.type).predicates}]
		     }
      Subj = {ExtractFeatures {VirtualString.toAtom 'subject_'#Nm} SubjFeatures}
   in
      Subj.name = Nm
      Subj.id = Id
      Subj.type = S.type
      Subj.rules = SubjRules
      Subj.init = SubjInit
      Subj.locals = {Record.toListInd Problem.behavior.(S.type).predicates}
      Subj
   end
in
  %   Conf.subSysNames = {Arity Problem.subjects.subSystems}
   {Record.forAllInd Conf.subjects proc{$ I Subj} Subj = {BuildSubject I} end}
   Conf.system = SysRules
   Conf.qsIds = {Map {Filter {Record.toList Conf.subjects}
		      fun{$ S} 
			 AllSubjects.(S.name).query
		      end}
		 fun{$ S} S.id end}
   Conf.qpreds = {FoldL Problem.config.optional
		  fun{$ Lst Prd}
		     Pred = {NamedPredToId Prd}
		  in
		     if {Member Pred Lst} then Lst else Pred|Lst end
		  end
		  {GetQPredsFromQSIds Conf} 
		 }
   %Conf.qPredValues = {List.map Conf.qpreds  fun{$ Prd} r(pred:Prd value:{FD.int 0#1}) end}  % structure to store query predicate values separately
   Conf.liveness = {Map Problem.goal.liv  fun{$ Prd} {NamedPredToId Prd} end}
   Conf.safety = {Map Problem.goal.saf  fun{$ Prd} {NamedPredToId Prd} end}
   Conf.init = {Map  Problem.config.facts 
		fun{$ Prd} {NamedPredToId Prd}
		end}
   Conf.problem = Problem
   Conf.subjectNames = SubjIdToName
   Conf
end

fun{NewConf Size}   % TODO CLEAN THIS UP
   config(problem:_
	  %startSign: _
	  system: _
	  subjects: {Tuple.make subjects Size}
	  behaviorArities: _
	  behaviorLabels: _
	  knowledgeArities: _
	  knowledgeLabels: _
	  size: Size
	  qsIds: _
	  qpreds:_ % to contain complete list of grounded query predicates
	  liveness: _
	  safety: _
	  init: _
	  traces: _
                % traces is list of grounded records with format: tr(pred:P value:I)
	        % traces is updated by this procedure only
	  oldTraces: {NewCell nil}
	  solution:_  % a list of relevant predicats that contains
		      % properties that MUST be FALSE to respect the safety properties
                      % properties that CAN be TRUE, and have an actual effect in the configuration
	              % THE LATTER IS NOT (NO LONGER?) CORRECT (except for fixpiont computations)
	  subjectNames:_
	  forFixpoint:_               % signal to start deriving zero query predicates from 1 calculated predicates
	  maxFixptZeroPreds:_         % list of all zero preds in maxfixpt
	  minFixptOnePreds:_          % list of all one preds in minfixpt
	 )
end


fun{IsQueryPred Pred Conf}
   {Member Pred Conf.qpreds}
end

fun{GetAllSubjectPredLabels Subj}
   {List.filter {Arity Subj}
    fun{$ Lbl}
       case Lbl
       of name then false
       [] id then false
       [] rules then false
       [] locals then false
       [] type then false
       [] init then false
       else true
       end
    end}
end

fun{ImplicitUnificationInRuleHead RuleHead}
   {ShowInfo 'ImplicitUnificationInRuleHead -->'}
   {Show {Record.map RuleHead fun{$ X} if {IsDet X} then X else '_' end
			      end}}
   {ShowInfo '<-- ImplicitUnificationInRuleHead'}
   false % FOR NOW TODO : implement this  CORRECTLY (How??)
end

fun{GetSubjectNonQueryNorInitLabels Subj Conf}
   {Filter {GetAllSubjectPredLabels Subj}
    fun{$ Lbl} {Not {IsQueryLabel Subj Lbl Conf}} andthen {Not {IsInitLabel Subj Lbl Conf}}
    end}
end


fun {IsQueryLabel Subj Lbl Conf}
   {List.some Conf.qpreds fun{$ Prd} Lbl == {Label Prd} andthen Prd.1==Subj.id
			  end}
end

fun {IsInitLabel Subj Lbl Conf}
   {List.some Conf.init fun{$ Prd} Lbl == {Label Prd} andthen Prd.1==Subj.id
			  end}
end

fun {LabelArity SubjId Lbl Conf}  % TODO: CHECK AND IMPROVE IMPLEMENTATION
   Arity                          
in                                
   for L#Ar in {Append
		{Append Conf.behaviorArities Conf.knowledgeArities}
		Conf.subjects.SubjId.locals}
      break:BR do
      if L==Lbl
      then Arity=Ar  {BR}
      end
   end
   if {IsDet Arity} then Arity else 0 end
end

fun{IsInitFact Pred Conf}
   {Member Pred Conf.init}
end


%distribution stuff __________________________


fun{NextDistributionPredGoodFirst Conf ?Trace ?Var} %return boolean indicating if var was found
   Rels = {Sort  {Filter Conf.qpreds %{AllQuerySubjectBehaviorPreds Conf}
		  fun{$ Prd}  {IsRelevantForDistributionPred Prd Conf}
		  end}
	   fun{$ Pr1 Pr2}
	      {FD.reflect.nbSusps {GetPred Pr1 Conf}} < {FD.reflect.nbSusps {GetPred Pr2 Conf}}  %ADDED IN EXPERIMENT
	   end}
in
   if Rels==nil then false
   else  Trace = Rels.1
      Var = {GetPred Trace Conf}
      true
   end
end

fun{NextDistributionPred Conf ?Trace ?Var} 
   {NextDistributionPredGoodFirst Conf ?Trace ?Var}
end

fun{ToBePrevented Conf}
   {Filter Conf.qpreds
    fun{$ Pred} {IsDetPredAndEquals Pred 0 Conf} 
    end}
%    SearchedSafetyGoals =  {Filter Conf.safety fun{$ Prd} {Member Prd Conf.qpreds} end}
% in
%    {FoldL SearchedSafetyGoals
%     fun{$ Lst Prd} if {Member Prd Lst} then Lst else Prd|Lst end
%     end
%     {ZeroPredSpec Conf}}
end

fun{ZeroPredSpec Conf}
   %{Map {Filter Conf.traces fun{$ Tr} Tr.value==0 end} fun{$ Tr} Tr.pred end}
   {Map {Filter Conf.solution fun{$ Tr} Tr.value==0 end} fun{$ Tr} Tr.pred end}
end

proc{Distribute Root}
   {List.forAll Root.liveness          % for efficiency: try more propagation, less search
    proc{$Pred} {TellPred Pred Root 1}  % since this may result in false liveness positives, 
    end}                                % the final calculation will be redone in Finalize
   {Distribute2 Root nil}
end

proc{Distribute2 Root Trcs}
   NextPred NextVar
in
   {Space.waitStable}
   if  {NextDistributionPred Root  NextPred NextVar}  
   then 
      choice  % Distributing LEFT
	 NextVar=1
	 {Distribute2 Root {Append Trcs [tr(pred:NextPred value:1)]}}
      []      % DISTRIBUTING RIGHT
	  %{ShowInfo "must not be 1 : "#{Label NextPred}}
	 NextVar=0
	 {Distribute2 Root {Append Trcs [tr(pred:NextPred value:0)]}}
      end
   else %Success
      Root.solution = {Map {Filter Root.qpreds % {AllQuerySubjectBehaviorPreds Root}
			    fun{$ Prd} {IsDetPred Prd Root} end}
		       fun{$ Prd} tr(pred: Prd value: {GetPred Prd Root}) end}
      Root.traces = Trcs
      {MarkSolution Root.solution}
   end
end


%---------calculation stuff ----
% TODO : get rid of calcdist
proc{CalculateSolutions Problem NumberOfSolutions CalcDist Time1 TimeOut ?TimeTaken ?AllSolutions ?GoodSolutions ?Completed}
   PreScript = {MakePreScript Problem}
   SO = {New ScollarSearch.object
	 script(PreScript MakeMinFixpt MakeMaxFixpt LearnFromFixpoints Distribute Finalize MoreSolutions)}
in
   {GetSolutionsFrom SO NumberOfSolutions Time1 TimeOut ?TimeTaken ?AllSolutions ?GoodSolutions ?Completed}
end

%TODO: integrate fixpoint calculation
% fun{CalculateFixpoint Problem MinB} % MinB == true => minfixpoint else maxfixpoint . 
%    PreScript = {MakePreScript Problem}
%    SO = {New ScollarSearch.object
% 	 script(PreScript MakeMinFixpt MakeMaxFixpt LearnFromFixpoints Distribute Finalize MoreSolutions)}
% in
%    if MinB then {SO getMinFixpt($)}
%    else {SO getMaxFixpt($)}
%    end
% end

proc{CalculateFixpoints Problem ?MinFp ?MaxFp}
   PreScript = {MakePreScript Problem}
   SO = {New ScollarSearch.object
	 script(PreScript MakeMinFixpt MakeMaxFixpt LearnFromFixpoints Distribute Finalize MoreSolutions)}
in
   MinFp =  {SO getMinFixpt($)}
   MaxFp = {SO getMaxFixpt($)}
end


%---- propagation stuff

fun{MakePreScript Problem}
   proc{$ Root}
      Root = {ParseConfig Problem}  % TODO: DOUBLE CHECK IF QUERY PREDICATES IN CONFIG ARE PARSED WELL
      % TODO: SUBJECT PRIVATE KNOWLEDGE THAT IS NOT IN ANY RULE'S HEAD SHOULD HAVE STRUCTURE
   end
end

proc{MakeMinFixpt Root}
   %{ShowInfo 'in MakeMinFixpt'}
   Root.minFixptOnePreds = nil  % only used while distributing
   Root.maxFixptZeroPreds = nil % only used while distributing
   Root.forFixpoint = true
   {Record.forAll Root.subjects proc{$ Subj}
				   {InstallRules Subj Root}
				end}
   {MakeComplete Root}
  % {Space.waitStable}
  % {ShowInfo 'done MakeMinFixpt'}
end

proc{MakeComplete Root}  % make everything needed
   %{ShowInfo 'in MakeComplete'}
   {ForAllSubjectLabels Root MakeLabelNeeded}
   %{ShowInfo 'done MakeComplete'}
end

proc{MakeMaxFixpt MinFixpt}          % maximize query predicates -- will not fail because no 0's were told yet
   %{ShowInfo 'in MakeMaxFixpt'}
   for Pred in MinFixpt.qpreds do    % assumes that MinFixpt.forFixpoint is true !
      {TellPred Pred MinFixpt 1}
   end
   %{Space.waitStable}
   %{ShowInfo 'done MakeMaxFixpt'}
end

proc{GetSolutionsFrom SO NumberOfSolutionsOrAll Time1 TimeOut ?TimeTaken ?AllSolutions ?GoodSolutions ?Completed}
   AbsoluteEndTimeSecs = Time1 + TimeOut
   NumberOfSolutions = case NumberOfSolutionsOrAll
		       of all then 0
		       [] one then 1
		       else NumberOfSolutionsOrAll
		       end % TODO adapt interface
   fun{NextSol Nmbr Tail} % returns boolean to indicate completion
      T1 T2 OK Sol
   in
      thread %calculation thread  
	 T1 = {Thread.this}
	 Sol = {SO next($)}
	 OK = unit
      end
      thread  %time out thread
	 T2 = {Thread.this}
	 {Time.delay (AbsoluteEndTimeSecs - {OS.time})*1000}
	 OK = unit
      end
      {Wait OK}
      try {Thread.terminate T1} catch _ then skip end
      try {Thread.terminate T2} catch _ then skip end
      if {IsDet Sol}
      then
	 if Sol==nil
	 then
	    Tail=nil
	    true
	 else
	    NextTail
	 in
	    Tail = Sol|NextTail
	    if Nmbr > 1 orelse Nmbr == 0 % stop when Nmbr == 1
	    then
	       {NextSol {Max Nmbr-1 0} NextTail}
	    else
	       NextTail = nil
	       true
	    end
	 end
      else
	 Tail= nil
	 false
      end
   end
in
   Completed = {NextSol NumberOfSolutions AllSolutions}
   TimeTaken = {OS.time} - Time1
   GoodSolutions = {Map {Filter AllSolutions
			 fun{$ Rec} {Label Rec} == finalized
			 end}
		    fun{$ R} R.1
		    end}
end

proc{LearnFromFixpoints MinFixpt MaxFixpt Current} % still no distribution
   Current.minFixptOnePreds = {DeterminedOnePreds MinFixpt}
   Current.maxFixptZeroPreds = {DeterminedZeroPreds MaxFixpt}
   Current.forFixpoint = false
   %{Inspect inLearnFromFixpoints}
   {Record.forAll Current.subjects proc{$ Subj}
				      {InstallRules Subj Current}
				   end}
   %{Inspect inLearnFromFixpointsAfterInstallRules}
   {List.forAll Current.safety proc{$ Pred} {TellPred Pred Current 0} end}
   %{Inspect doneLearningFromFixpoints}
end


proc{Finalize Solution Undistributed} % port query preds from Solutions to Undistributed -- no Liveness was enforced yet!
                                      % also port the traces: Undistributed has no traces and needs them to present the solution
   Stable
in
   %{ShowInfo 'in Finalize'}
   try
      Undistributed.traces = Solution.traces       % just for keeping record
      Undistributed.solution = Solution.solution
      %Undistributed.oldTraces := Solution.oldTraces % just for keeping record  % !!NOT ALLOWED, WHY NOT??
      %{ShowInfo 'transferred traces'}
      for Pred in Solution.qpreds do
	 thread% just for keeping record
	    Val =  {GetPred Pred Solution}   % TODO: make sure every query predicate has structure to hold it!
	 in
	    {Wait Stable}
	    if {IsDet Val}    % don't unify Val !!!
	    then {TellPred Pred Undistributed Val}
	    else {TellPred Pred Undistributed 1}  % undefined qpreds remaining are all maximized, including knowledge qpreds in config part (!)
	    end
	 end
      end
      {Space.waitStable} % is OK: current space has no distributor !
      Stable = unit
      {Space.waitStable}
      {MakeComplete Undistributed} % is OK: current space has no distributor !
   catch E then
      {ShowInfo 'Unexpected Failure when Finalizing:'}
      {Show E}
   end
   {Space.waitStable} % is OK: current space has no distributor !
   %{ShowInfo 'MakeComplete succeeded'}
   %{ShowInfo 'Undistributed.liveness  = --->'}
   %{Show Undistributed.liveness}
   % TODO : check if Space.waitStable can cause interaction with Space.ask
   %{Inspect liveness#(Undistributed.liveness)}
   for Pred in Undistributed.liveness do % fail when liveness pred not already 1  (liveness pred that is also a query predicate will always be 1)
      if {IsDetPredAndEquals Pred 1 Undistributed} 
      then skip
      else fail
      end
   end
end

proc{MoreSolutions Old New} % all further solutions must have at least one 0 replaced by a 1
                            % to avoid being a subsolution
                            % this goes even if the current solution is not alive.
   (New.oldTraces) := {ZeroPredSpec Old}|@(Old.oldTraces)
   {ForAll @(New.oldTraces)
    proc{$ OldZeroPreds}
       {FD.sum {Map OldZeroPreds fun{$ Pred} {GetPred Pred New} end}
	'>:' 0}
    end}
end

   
% proc{CalculateSolutionsQ  QueryScript OneOrAll CalcDist Time1 TimeOut ?TimeTaken ?AllSolutions ?GoodSolutions ?Completed}
%    T1 T2 Out OutCell={NewCell nil} Done
%    %if Options.debug then {Show inCalculateSolutionsQ} end
%    SearchObject
% in
%    {Show enteringFinalCalculationAtTimeZeroPlus({OS.time}-Time1)}
%    thread %calculation thread
%       %try 
%       T1 = {Thread.this}
%       SearchObject =  if OneOrAll==one% andthen Options.'cond'
%                                % INCOMPLETE CONDITION: SHOULD BE MORE RESTRAINED (LIVENESS)
% 		      then {New FindObject script(QueryScript)}
% 		      else {New Search.object script(QueryScript MoreSolutions rcd:CalcDist)}
% 		      end
%       for break:BR
%       do 
% 	 Next = {SearchObject next($)}
%       in
% 	 if Next==nil  
% 	 then
% 	    Out=true|@OutCell
% 	    Done = true
% 	    {BR}
% 	 else
% 	    OutCell := {Append @OutCell Next}
% 	    if OneOrAll==one then
% 	       Out=true|@OutCell
% 	       Done = true
% 	       {BR}
% 	    end
% 	 end
%       end
% %       catch E then {Show somethingWrongInCalculateSolutionsQ(E)} % catch the terminate error thrown by Thread.terminate   
% % 	 OutCell:=Value.failed 
% %       end
%    end
%    thread  %time out thread
%       T2 = {Thread.this}
%       {Time.delay TimeOut}
%       Done = false
%       try Out=false|@OutCell catch E
%       then {Show couldNotAssignExtractSolutionsUponTimeOut(calculateSolutionsQ:E)}
%       end
%    end
%    {MarkProgress 1000 Done}
%    %{Wait Done}
%    try {Thread.terminate T1} catch _ then skip end
%    try {Thread.terminate T2} catch _ then skip end
%    {Show doneWaiting}
%    Completed|AllSolutions = case Out
% 			    of true|_ then Out
% 			    [] false|_ then Out
% 			    else false|Out
% 			    end
%    GoodSolutions = {Filter AllSolutions
% 		    fun{$ Sol} Sol.alive
% 		    end}
%    TimeTaken = {OS.time} - Time1
%    %if Options.'local' andthen Options.debug then {Inspector.inspect GoodSolutions} end
% end

% --- moved over here from scollarhtml.oz

fun{Permute N1 N2}
   %if Options.debug then {Show permute('N1':N1 'N2':N2)} end
   Head Tail={NewCell Head}
in
   {Loop.multiFor
    {Map {List.number 1 N1 1} fun{$ _} 1#N2#1 end}
    proc{$ X} @Tail=X|_ Tail:=@Tail.2 end}
   @Tail=nil
   Head
end

fun{AllPredPermutations Id Lbl Ar Size}
   {Map {Permute Ar-1 Size}
    fun{$ Lst} {List.toTuple Lbl Id|Lst} end
   }
end

proc{MarkSolution Sol}
   {ShowInfo '-----> marking Solution'}
end

proc{MarkProgress Interval StopSignal} %StopSignal is undefined variable that is set to true when
   X
in
   thread {Time.delay Interval}
      X=unit
   end
   case {Record.waitOr r(done:StopSignal continue:X)}
   of continue then
      %{ShowInfo '>>>>> time interval elapsed'}
      {MarkProgress Interval StopSignal}
   else skip
   end
end