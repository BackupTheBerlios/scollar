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
   Conf.knowledgeLabels = {Map {Append Problem.'declare'.state
				Problem.'declare'.knowledge}
			   fun{$ Decl} Decl.label end}
   Conf.behaviorArities = {Map Problem.'declare'.behavior fun{$ Decl} (Decl.label)#(Decl.arity) end}
   Conf.knowledgeArities =  {Map {Append Problem.'declare'.state
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
      if {IsDet Subj.Feat} andthen {IsList Subj.Feat}
      then case {Member Pred Subj.Feat} of true then 1 [] false then 0 end
      else
	 thread {GetPredValue Subj.Feat {Record.toList Pred}.2} end  
      end
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
   Val = {GetPred Prd Conf}  % may cause rules to be installed (not when both sides are undetermined)
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
   elseif {IsDet Subj.Feat} andthen ({IsInt Subj.Feat} orelse {IsList Subj.Feat})then true
   else
      {IsDetPredValue Subj.Feat {Record.toList Pred}.2}
   end
end
fun{IsDetPredValue Val Keys}   % DOES NOT make structure needed             
   case Keys                   % NEVER blocks 
   of nil then {IsDet Val}     % IS UTTERLY UNDETERMINISTIC    
   [] Key|T then              
      {IsDet Val} andthen ({IsInt Val} orelse  {IsList Val} orelse  {IsDetPredValue Val.Key T}) 
   end
end
%----  
proc{MakeLabelNeeded Subj Lbl Ar Conf}
   if {IsEnumeratedLabel Lbl Subj.id Conf} then skip
   else
   %{Show 'in MakeLabelNeeded'(subjId: Subj.id lbl:Lbl ar:Ar confSize: Conf.size)}
   %{Show 'hasFeature'(subjId: Subj.id trueOrFalse:{HasFeature Subj Lbl})}
      if {Not {HasFeature Subj Lbl}} then skip  % always zero! TODO: double check that all query predicates get at least feature structure
      elseif {IsDet Subj.Lbl} andthen {IsInt Subj.Lbl} then skip
      else
	 {MakePredsNeeded Subj.Lbl Ar-1 Conf.size} 
      end
   %{ShowInfo 'done MakeLabelNeeded'}
   end
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

%----
fun{IsDetPredAndEquals Pred V Conf}   % Asked only after MakeComplete was called on Conf. Structure should be complete by now
   Feat = {Label Pred}
   Subj = Conf.subjects.(Pred.1)
in                                          
   if {Not {HasFeature Subj Feat}} then V == 0  % TODO: double check that all query predicates get at least feature structure
   elseif {Not {IsDet Subj.Feat}} then V == 0
   elseif Subj.Feat == V then true
   elseif {IsList Subj.Feat} then  {Member Pred Subj.Feat}==(V==1)
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
      if {IsDet Subj.Feat} andthen {IsInt Subj.Feat} then Subj.Feat
      elseif {IsDet Subj.Feat} andthen {IsList Subj.Feat}
      then if {Member Pred Subj.Feat}
	   then 1
	   else 0
	   end
      else
	 {GetPredValueAfterCalculation Subj.Feat {Record.toList Pred}.2}
      end
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

fun{GetMatchingAlternatives Facts Prd}
   TemplateVars = {Filter {Record.toList Prd} IsAtom}
in
   for Fact in Facts collect:C
   do
      NewConstants = {Record.adjoinList vars {Map TemplateVars fun{$ Atm} Atm#_ end}}
      Trial = {Record.map Prd fun{$ X} if {IsInt X} then X else NewConstants.X end
			      end}
   in
      try
	 Trial = Fact % unification as test
	 {C NewConstants}
      catch _ then skip
      end
   end
end

fun{GetEnumeration Lbl SubjId Conf}
   Val = Conf.subjects.SubjId.Lbl
in
   if {IsDet Val} then
      if Val == 0 then nil
      else Val % should be list
      end
   else raise 'Expected a List as value in GetEnumeration' end
      nil % should not happen
   end
end

proc{TestConditionsEnumerated SortedPreds Vars Conf RuleHeadValue} % RuleHeadValue is 0#1 FD variable
   % first condition Prd in SortedPreds is an enumerated predicate with Prd.1 instantiate (integer)
   % it is either a NeverLabel, an AlwaysLabel or a ConfigOnlyLabel for the subject with id Prd.1
   Prd|T = SortedPreds
in
   if {IsAlwaysLabel {Label Prd} Prd.1 Conf} then {TestConditions T Vars Conf RuleHeadValue}
   else
      MatchingAlternatives = {GetMatchingAlternatives {GetEnumeration {Label Prd} Prd.1 Conf} Prd}
      % MatchingAlternatives is now a list of records, each specifying a valid variable binding for all unbound variables in Prd
   in
      if MatchingAlternatives == nil then RuleHeadValue = 0
      elseif T == nil then RuleHeadValue = 1
      else 
          % existential quantification over MatchingAlternatives
	  % HERE WE  OPTIMISE THINGS BY USING ENUMERATIONS FOR CONFIG-ONLY PREDICATES AND NEVER-PREDICATES
	 PartialValues = {FD.tuple '#' {Length MatchingAlternatives} 0#1}
      in
	 {FD.sum PartialValues '>=:' RuleHeadValue} % close world
	 {List.forAllInd MatchingAlternatives proc{$ I Alt}
						 NewVars = {Record.adjoin Vars Alt}
						 RemainingPreds =  {Map T
								    fun{$ Pr} {Record.map Pr
									       fun{$ V} if {IsInt V} then V else NewVars.V end end}
								    end}
					      in
						 RuleHeadValue >=: PartialValues.I		 
						 {TestConditions RemainingPreds NewVars Conf PartialValues.I}
					      end}
      end
   end
end



fun{IsAlwaysLabel Lbl SubjId Conf}
   Val = Conf.subjects.SubjId.Lbl
in
   {IsDet Val} andthen Val==1 % you should never have to wait on an alwaysLabel
end

fun{IsEnumeratedLabel Lbl SubjId Conf}
   Val = Conf.subjects.SubjId.Lbl
in
   {IsDet Val} andthen {IsInt Val} orelse {IsList Val} % you should never have to wait on an alwaysLabel
end


fun{IsEnumeratedPred Prd Conf}
   SubjId = Prd.1
in
   {IsInt SubjId} andthen  {IsEnumeratedLabel {Label Prd} SubjId Conf}
end



% We defer existential quantification until it is needed for the first Pred !
proc{TestConditions RawPreds Vars Conf RuleHeadValue} % RuleHeadValue is 0#1 FD variable
   % for optimisation: sort so that first the predicates that have less non-instantiated arguments or not-yet-determined values are tested
   % due to recursion, sort is re-executed for every predicate and then in every existential quantification step
   Preds = {PartialSorted RawPreds Conf}  
in
   case Preds
   of Prd|T then
      if {IsEnumeratedPred Prd Conf} then {TestConditionsEnumerated Preds Vars Conf RuleHeadValue}
      else
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
	   % HERE WE CAN OPTIMISE THINGS BY USING ENUMERATIONS FOR CONFIG-ONLY PREDICATES
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
      end
   [] nil then RuleHeadValue = 1 % for body-less rules
   end
end





proc{Instantiate Rule Head Conf RuleHeadValue} % Head and all preds in Rule are global!!
                                              % Head is COMPLETELY instantiated clone of Rule.head !!
   % trying to allow implicit unification of parameters with same name in head is TOO LATE HERE !!
   % implicit unification has been taken care of in InstantiateDisjuction (see there)
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
            % BUT IF Rule.head CONTAINS TWICE THE SAME VARIABLE, THIS WOULD CAUSE FAILURE OF THE SPACE
            % INSTEAD IT SHOULD JUST CAUSE THE RULE TO FAIL DUE TO A BROKEN IMPLICIT EQUALITY CONDITION!
            % THEREFOR WE DO THIS IN A try catch
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
      
    % currently we don't close the world when deriving qPreds, to allow underivable qPreds to become 1 by choice
    % problem: Q A => Q1; and Q1 => S;  with S==0 and A==1 should derive that Q==0
    % we need to be able to close the world for Q when Q's value was derived (possibly from closure)
    % we create a by-choice-Q variable different from Q for every qPred Q
    % and we add by-choice-Q to the sum when closing the world on Q
    % (doing so will cause by-choice-Q to become 0 if Q becomes 0 by closure)
    % upon stability, before distribution properly, set all undefined by-choice-Q's for which Q is defined to 0
    % (doing so will close the world properly on Q: by-choice-Q's influence in the sum will vanish)
    % do this repeatedly when necessary, because of the possible effects of closing the world
    % when distributing, first try Q's that have less rules deriving Q. (?!)
    % to distribute, choose an undefined Q, unify it with by-choice-Q, and set to 1 (or to 0 when backtracking)
    % problem now solved:  Q A => Q1; and Q1 => S;  with S==0 and A==1
    % from closing world on Q1 : sum(Q,0,by-choice-Q1) >=: Q1 with Q1==1 derived by closing world on S
    % upon stability, by-choice-Q1 will be set to 0 and thus Q will become 1.
   end
end

proc{InstantiateWhenNeeded SubjId Lbl Rules Conf}
  % Rules can be nil now
  % all rules are global and have same head (modulo names of parameters)!!
   Args = {LabelArity SubjId Lbl Conf}-1
in
   Conf.subjects.SubjId.Lbl
   = {LazyTuple Conf.size Args
      {Record.adjoinAt Lbl 1 SubjId} % seed for Lazytuple: eg. access(SubjId) to be completed to access(SubjId 1) etc
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

proc{CleanUpRules Subj Conf  ?AlwaysLabels ?NeverLabels ?RulesToInstall}
   AllRules = {Append Conf.system Subj.rules}
   SubjectNonQueryNorInitLabels = {GetSubjectNonQueryNorInitLabels Subj Conf}
   CellNoChange = {NewCell false}
   CellRulesToInstall =  {NewCell AllRules}
   CellAlwaysLabels = {NewCell nil}
   CellNeverLabels = {NewCell nil}
in
   for until:@CellNoChange do
      PrevNeverLabelsCnt = {Length @CellNeverLabels}
   in
      CellNoChange:=true
      CellNeverLabels := for Lbl in SubjectNonQueryNorInitLabels collect:C do  % don't touch query predicates or init predicates
			    if  ({Not {Member Lbl @CellAlwaysLabels}}
				 andthen {List.all @CellRulesToInstall fun{$ R} {Label R.head} \= Lbl end})
			    then
			       {C Lbl}
			    end
			 end
      if  {Length @CellNeverLabels} > PrevNeverLabelsCnt then CellNoChange := false end
      CellRulesToInstall := for R in @CellRulesToInstall collect:C do
			       Head = R.head
			       HeadLbl = {Label Head}
			       HeadIsRegular = {Not {ImplicitUnificationInRuleHead R.head}}
			    in
			    % {ShowInfo ">>>>> iteration start in CleanUpRules"}
			       if {List.all R.body
				   fun{$ Prd}
				      HeadIsRegular andthen Head.1 == Prd.1 andthen {Member {Label Prd} @CellAlwaysLabels}
				   end}  % works also when body == nil
			       then   % disregard the rule, it has an alwayslabel in its head
				  CellNoChange := false
				  if {Not {Member HeadLbl @CellAlwaysLabels}}
				  then CellAlwaysLabels := HeadLbl|@CellAlwaysLabels
				  end
			       elseif {List.some R.body
				       fun{$ Prd}
					  R.head.1 == Prd.1 andthen {Member {Label Prd} @CellNeverLabels} 
				       end}
			       then
				  CellNoChange := false % disregard the rule, it has a neverlabel in its body
			       else {C R}
			       end
			     % {ShowInfo ">>>>> iteration end in CleanUpRules"} 
			    end
   end
   %{ShowInfo "<<<<<< iteration ALMOST  done in CleanUpRules"} 
   AlwaysLabels = @CellAlwaysLabels
   NeverLabels = @CellNeverLabels
   RulesToInstall = @CellRulesToInstall
   %{ShowInfo "<<<<<< iteration done in CleanUpRules"} 
end


% proc{CleanUpRules Subj SubjectLabels Conf ?AlwaysLabels ?NeverLabels ?InstallRules}
%    % should take global alwayslabels and global neverlabels into account too
%    AllRules = {Append Conf.system Subj.rules}
%    SubjectNonQueryNorInitLabels = {GetSubjectNonQueryNorInitLabels Subj Conf}
%    CellNoChange = {NewCell false}
%    CellInstallRules =  {NewCell AllRules}
%    CellAlwaysLabels = {NewCell nil}
%    CellNeverLabels = {NewCell nil}
% in
%    for until:@CellNoChange do
%       PrevNeverLabelsCnt = {Length @CellNeverLabels}
%    in
%       CellNoChange:=true
%       CellNeverLabels := for Lbl in SubjectNonQueryNorInitLabels collect:C do  % don't touch query predicates or init predicates
% 			    if {Not {Member Lbl @CellAlwaysLabels}}
% 			       andthen {List.all @CellInstallRules fun{$ R} {Label R.head} \= Lbl end}
% 			    then
% 			       {C Lbl}
% 			    end
% 			 end
%       if  {Length @CellNeverLabels} > PrevNeverLabelsCnt then CellNoChange := false end
%       CellInstallRules := for R in @CellInstallRules collect:C do
% 			    % {ShowInfo ">>>>> iteration start in CleanUpRules"} 
% 			     if  {Not {ImplicitUnificationInRuleHead R.head}} % e.g. not for access(x x) or did.getFrom(x y y) because the head is too specific
% 				andthen {List.all R.body
% 				  fun{$ Prd}
% 				     R.head.1 == Prd.1 andthen {Member {Label Prd} @CellAlwaysLabels} 
% 				  end}  % works also when body == nil
% 			     then   % disregard the rule, it has an alwayslabel in its head
% 				NewAlwaysLabel = {Label R.head}
% 			     in
% 				CellNoChange := false
% 				if {Not {Member NewAlwaysLabel @CellAlwaysLabels}}
% 				then CellAlwaysLabels := NewAlwaysLabel|@CellAlwaysLabels
% 				end
% 			     elseif {List.some R.body
% 				     fun{$ Prd}
% 					R.head.1 == Prd.1 andthen {Member {Label Prd} @CellNeverLabels} 
% 				     end}
% 			     then
% 				CellNoChange := false % disregard the rule, it has a neverlabel in its body
% 			     else {C R}
% 			     end
% 			     % {ShowInfo ">>>>> iteration end in CleanUpRules"} 
% 			  end
%    end
%    AlwaysLabels = @CellAlwaysLabels
%    NeverLabels = @CellNeverLabels
%    InstallRules = @CellInstallRules
%   % {ShowInfo "<<<<<< iteration done in CleanUpRules"} 
% end
proc {InstallSubjectRules Subj Conf} % will close the world by using disjunctive conditions, except when deriving query predicates
                              % detects always derived and never derived properties (the latter except for query predicates)
   AlwaysLabels NeverLabels RulesToInstall
   SubjectLabels = {GetAllSubjectPredLabels Subj}
   Extremes NonExtremes SubjectConfigOnlyLabels
in
   {CleanUpRules Subj Conf ?AlwaysLabels ?NeverLabels ?RulesToInstall}
   %{Inspect 'AlwaysLabels'#(Subj.name)#AlwaysLabels}
   %{Inspect 'NeverLabels'#(Subj.name)#NeverLabels}
   SubjectConfigOnlyLabels = {Filter {GetConfigLabels Subj Conf}
			      fun{$ Lbl}  %{LabelArity Subj.id Lbl Conf} > 1 andthen
				 {List.all RulesToInstall fun{$ R}  {Label R.head} \= Lbl end}
			      end}
   %{Inspect 'SubjectConfigOnlyLabels'#Subj.name#SubjectConfigOnlyLabels}
   Extremes = {Flatten [AlwaysLabels NeverLabels SubjectConfigOnlyLabels]}
   NonExtremes = {Filter SubjectLabels fun{$ Lbl}  % starting from would have the side-effect that some initialisation is not done
					  {Not {Member Lbl Extremes}}
				       end}
   Subj.derivedPredLabels = NonExtremes
   for Lbl in NeverLabels do Subj.Lbl = 0 end % OK even for fixpoints
   for Lbl in AlwaysLabels do Subj.Lbl = 1 end
   for Lbl in SubjectConfigOnlyLabels do
      if {LabelArity Subj.id Lbl Conf} > 1
      then
	 Subj.Lbl = {Filter Conf.subjects.(Subj.id).init fun{$ Fact} {Label Fact} == Lbl end}
      else Subj.Lbl = 1
      end
   end
   for Lbl in NonExtremes do                    % we call InstantiateWhenNeeded for every Label here because
      {InstantiateWhenNeeded Subj.id Lbl           % it should lazily build the structure
%      {Filter AllRules fun{$ R} R.body \= nill andthen {Label R.head} == Lbl
%			end}  % can result in nil : for query predicates with no (bodyless) rules
       {Filter RulesToInstall fun{$ R} {Label R.head} == Lbl end}
       Conf}
   end
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


%------------ optimisation for underived predicates ------------
%
% body predicates that are not derived but present in config (globally for system rules, locally for behavior rules)
%         (query predicates for maxconfig are excluded here) 
%  - will be instantiated by enumerating the facts for the current subject during rule instantiation
%  - should be the first predicates in the body of every rule-being-instantiated that contains them
%  - will be stored in a list instead of in a table
%  - facts with this label will never be set nor be (made) needed during fixpoint computations or during completion.
%  - will not be shown in the fixpoint or detailed solution table (it's obvious, they were stated)
%  - since they are not query predicates they will not show up in the solutions overview either.
%
%
% rules with only such body predicates will thus, upon instantiation, make nothing needed.
% rules with never-labels in their body should not be considered
%  - this may result in more never-labels and more config-only labels
% always-labels should be removed from the rules.
%  - this may result in more always-labels.
% this means, we should calculate a fixpoint for always-labels, neverl-labels and config-only labels
%
% Thus, we strive for optimisation without having to introduce forward chaining
%
%
% 1) Collect all rules globally
%    Collect headlabels
%    For every label L not in queryLabels
%       if L not in initlabels and there is no rule with L in head and not in body
%       then add L to neverLabels
%       elseif L in initLabels and no rule has L in head
%       then add L to configOnlyLabels
%       end
%   For every Rule R 
%       if $ has a neverLabel in is body then remove R
%   Go to 1) until fixpt reached
%
%
%
%
% 2) For every Subject S
%      Collect rules for S
%      Collect headlabels(S) for rules(S)
%      For every label L not in queryLabels nor globalNeverlabels nor headLabels
%         if L in initlabels(S)
%         then add L to configOnlyLabels(S)
%         else add L to neverLabels(S)
%  2a) For every label L in HeadLabels(S)
%         if L is in a bodyless rule R that has a head with no implicit unification
%         then add L to alwaysLabels(S)
%      For every behavior rule R in Rules(S)
%         remove the alwaysLabels from the rules
%      Go to 2a) until fixpt reached
%
%
% for fixpt and completion of solutions, for every subject S:
%   - only make headlabels(S) and querylabels(S) needed
%   - only show headlabels(S) and querylabels(S) in fixpt tables and solution detail tables
%-----------------------------------------------------------------

fun{GetConfigLabels Subj Conf} % we do NOT include optional (query) facts, not even for maxfixpt
   % we may want to keep predicates with arity =< 2 as they were !
   {FoldLTail {GetSubjectNonQueryInitLabels Subj Conf}
    fun{$ Result Tail} if % {LabelArityd Subj.id Tail.1 Conf} =< 2 orelse
			  {Member Tail.1 Tail.2} %remove duplicates, just to be sure.
		       then Result
		       else Tail.1|Result
		       end
    end
    nil}
end

fun{GetSubjectNonQueryInitLabels Subj Conf}
   {Filter {GetAllSubjectPredLabels Subj}
    fun{$ Lbl} {Not {IsQueryLabel Subj Lbl Conf}} andthen {IsInitLabel Subj Lbl Conf}
    end}
end





%--------------- forward chaining stuff (for fixpoints and forward chainging rules) ----
%------THIS IS NOT A GOOD IDEA (better: see above) --------------
%
% watch out for interference with always and neverlabels!
%
% fun{GetConfigLabels Conf} % we should include optional facts in maxfixpt
%    {FoldLTail {Map  Conf.program.config.facts %{Append Conf.program.config.facts Conf.program.config.optional}
% 	       fun{$ Prd} {Label Prd} end}
%     fun{$ Result Tail} if {Member Tail.1 Tail.2}
% 		       then Result
% 		       else Tail.1|Result
% 		       end
%     end
%     nil}
% end


% fun{GetInitLabels Conf} %no duplicates ... WRONG (on safe side) in assuming that private predicates are globally unique.
%    {FoldLTail {Map Conf.init fun{$ Prd} {Label Prd} end}
%     fun{$ Result Tail} if {Member Tail.1 Tail.2} then Result
% 		       else Tail.1|Result
% 		       end
%     end
%    nil}
% end


% fun{FWChainingRules Conf} % WRONG  (on safe side) : relies on private predicates being globaly unique.
%    AllRules = {Flatten Conf.system|{Map {Record.toList Conf.subjects} fun{$ Subj} Subj.rules end}}  
%    PushLabels = {Filter {GetInitLabels Conf}
% 		 fun{$ Lbl} {List.all AllRules
% 			     fun{$ Rule} {Label  Rule.head} \= Lbl end}
% 		 end}
% in
%    {Filter AllRules
%     fun{$ Rule}
%        {List.all Rule.body fun{$ Prd} {Member {Label Prd} PushLabels} end}
%     end}
% end


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
	    fun{$ State Lst2}
	       {List.toTuple Lbl Id|State}|Lst2
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
		      [[name id rules locals type init derivedPredLabels]
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
      %Subj.derivedPredLabels will be filled later.
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
       [] derivedPredLabels then false
       else true
       end
    end}
end

fun{ImplicitUnificationInRuleHead RuleHead}
   Lst = {Map {Record.toList RuleHead}
	  fun{$ X} if X=='_' then {NewName} else X end
	  end}
   fun{Check Tail}
      case Tail
      of nil then false
      [] X|T then if {Member X T} then true
		  else {Check T}
		  end
      end
   end
   Unif = {Check Lst}
in
%    {ShowInfo 'ImplicitUnificationInRuleHead -->'}
%    {Show {Record.map RuleHead fun{$ X} if {IsDet X} then X else '_' end
% 			      end}#Unif}
%    {ShowInfo '<-- ImplicitUnificationInRuleHead'}
   Unif
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
		    % andthen {List.all Trace fun{$ Tr} Tr.pred \= Prd end} % filtering because of strange result when using reportprogress 
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


ProgressReportDepth = 6
proc{Distribute Root}   {List.forAll Root.liveness          % for efficiency: try more propagation, less search
    proc{$Pred} {TellPred Pred Root 1}  % since this may result in false liveness positives, 
    end}                                % the final calculation will be redone in Finalize
   {Distribute4 Root nil 0 ProgressReportDepth}
end

proc{Distribute2 Root Trcs}
   NextPred NextVar
in
   {Space.waitStable}
   if  {NextDistributionPred Root NextPred NextVar}  
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
   end
end

proc{Distribute4 Root Trcs Count Depth} % in upper nodes of searchtree only, to mark progress
   if Depth =< 0
   then {Distribute2 Root Trcs}
   else
      NextPred NextVar
   in
      {Space.waitStable}
      if  {NextDistributionPred Root NextPred NextVar}  
      then 
	 choice  % Distributing LEFT
	    NextVar=1
	    %{Show {Map {Append Trcs [tr(pred:NextPred value:1)]} fun{$ Tr} Tr.value end}}
	    {Distribute4 Root {Append Trcs [tr(pred:NextPred value:1)]} Count {Max Depth-1 0}}
	 []      % DISTRIBUTING RIGHT
	  %{ShowInfo "must not be 1 : "#{Label NextPred}}
	    NextVar=0
	    {ReportProgress Count + {Pow 2 (Depth-1)}}
	    % {Show {Map {Append Trcs [tr(pred:NextPred value:0)]} fun{$ Tr} Tr.value end}}
	    {Distribute4 Root {Append Trcs [tr(pred:NextPred value:0)]} Count + {Pow 2 (Depth-1)} {Max Depth-1 0}}
	 end
      else %Success
	 Root.solution = {Map {Filter Root.qpreds % {AllQuerySubjectBehaviorPreds Root}
			       fun{$ Prd} {IsDetPred Prd Root} end}
			  fun{$ Prd} tr(pred: Prd value: {GetPred Prd Root}) end}
	 Root.traces = Trcs
      end
   end
end


%---------calculation stuff ----

proc{CalculateSolutions Problem NumberOfSolutions Time1 TimeOut ?TimeTaken ?AllSolutions ?GoodSolutions ?Completed}
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
   %{Inspect maxFp#MaxFp}
end


%---- propagation stuff

fun{MakePreScript Problem}
   proc{$ Root}
      Root = {ParseConfig Problem}  % TODO: DOUBLE CHECK IF QUERY PREDICATES IN CONFIG ARE PARSED WELL
      % TODO: SUBJECT PRIVATE KNOWLEDGE THAT IS NOT IN ANY RULE'S HEAD SHOULD HAVE STRUCTURE
   end
end


proc{InstallConfigRules Conf}
   {Record.forAll Conf.subjects proc{$ Subj}
				   {InstallSubjectRules Subj Conf}
				end}
end


proc{MakeMinFixpt Root}
   {ShowInfo 'in MakeMinFixpt'}
   Root.minFixptOnePreds = nil  % only used while distributing
   Root.maxFixptZeroPreds = nil % only used while distributing
   Root.forFixpoint = true
   %{Inspect 'FWChainingRules '#{FWChainingRules Root}}
   {InstallConfigRules  Root}
   {MakeComplete Root}
  % {Space.waitStable}
   {ShowInfo 'done MakeMinFixpt'}
end

proc{MakeComplete Conf}  % make everything needed
   {Record.forAll Conf.subjects
    proc{$ Subj}
       {ForAll Subj.derivedPredLabels
	proc{$ Lbl}
	   Ar =  {LabelArity Subj.id Lbl Conf}
	in
	   {MakeLabelNeeded Subj Lbl Ar Conf}
	end}
    end}   
end

proc{MakeMaxFixpt MinFixpt}          % maximize query predicates -- will not fail because no 0's were told yet
   %{ShowInfo 'in MakeMaxFixpt'}
   for Pred in MinFixpt.qpreds do    % assumes that MinFixpt.forFixpoint is true !
      {TellPred Pred MinFixpt 1}
   end
   %{Space.waitStable}
   %{ShowInfo 'done MakeMaxFixpt'}
end

% proc{MakeMaxFixptFwds MinFixpt}          % maximize query predicates -- will not fail because no 0's were told yet
%    %{ShowInfo 'in MakeMaxFixpt'}
%    for Pred in MinFixpt.qpreds do    % assumes that MinFixpt.forFixpoint is true !
%       {TellPred Pred MinFixpt 1}
%    end
%    %{Space.waitStable}
%    %{ShowInfo 'done MakeMaxFixpt'}
% end

proc{GetSolutionsFrom SO NumberOfSolutionsOrAll Time1 TimeOut ?TimeTaken ?AllSolutions ?GoodSolutions ?Completed}
   AbsoluteEndTimeSecs = Time1 + TimeOut
   NumberOfSolutions = case NumberOfSolutionsOrAll
		       of all then 0
		       [] one then 1
		       else NumberOfSolutionsOrAll
		       end % TODO adapt interface
   fun{NextSol Nmbr Tail} % returns boolean to indicate completion
      T1 T2 T3 T1Done T2Done T3Done OK Sol
   in
      thread %calculation thread  
	 T1 = {Thread.this}
	 Sol = {SO next($)}
	 T1Done=unit
      end
      thread  %time out thread
	 T2 = {Thread.this}
	 if TimeOut == 0
	 then {Wait _}
	 else {Time.delay (AbsoluteEndTimeSecs - {OS.time})*1000}
	 end
	 T2Done = unit
      end
      thread  %interrupt thread
	 T3 = {Thread.this}
	 {Wait @InterruptCell}
	 T3Done = unit
      end
      OK = {Record.waitOr r(T1Done T2Done T3Done)}
      try {Thread.terminate T1} catch _ then skip end
      try {Thread.terminate T2} catch _ then skip end
      try {Thread.terminate T3} catch _ then skip end
      case OK
      of 1 then
	 {ShowInfo "Regular thread ending"}
	 if Sol==nil
	 then
	    Tail=nil
	    true
	 else
	    NextTail
	 in
	    {MarkSolution Sol}
	    Tail = Sol|NextTail
	    if Nmbr > 1 orelse Nmbr == 0 % stop when Nmbr == 1
	    then
	       {NextSol {Max Nmbr-1 0} NextTail}
	    else
	       NextTail = nil
	       true
	    end
	 end
      [] 2 then {ShowInfo "timed out"}
	 Tail = nil
	 false
      else
	 {ShowInfo "INTERRUPTED"}
	 Tail = nil
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
   {InstallConfigRules Current}
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
   {Show'-----> marking Solution'#{Label Sol}}
   % {@ProgressBarCell incrSolCnt({Label Sol}==finalized)}
   {AddSolCnt}
end

proc{MarkProgress Interval DoThis StopSignal} %StopSignal is undefined variable that will be set to stop this
   X
in
   thread {Time.delay Interval}
      X=unit
   end
   case {Record.waitOr r(done:StopSignal continue:X)}
   of continue then
      %{ShowInfo '>>>>> time interval elapsed'}
      thread {DoThis} end
      {MarkProgress Interval DoThis StopSignal}
   else skip
   end
end


proc{ReportProgress Count}
   %Str = {VirtualString.toString "Progress: "#Count#"/"#{Pow 2 ProgressReportDepth}#"th of search space explored"}
   % if {Not @ProgressBarCell == nil} then {@ProgressBarCell setRatio(Count {Pow 2 ProgressReportDepth})} end
%in
%   {ShowInfo Str}
  {ReplyStatus Count#'/'#{Pow 2 ProgressReportDepth}}
end
