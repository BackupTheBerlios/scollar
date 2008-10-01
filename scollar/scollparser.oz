%%%%%%%%%%%%%%%%%%
%% Copyright  Fred Spiessens  & Yves Jaradin 
%% see www.evoluware.eu
% 
%
% changes 
% - 23-Dec-2006 fred : syntax now supports:may.do(B,X) in system rules
% - 26-Nov-2007 fred : error msg now includes line and col numbers
% - 26-Jun-2008 fred : "permission" replaced by "state"
%
%
%
%%%%%%%%%
functor
export ScollParse  ToKernel  Analyze
define
%declare

%  proc{Test}
%     I = {Inspector.new unit}
%     {I configureEntry(widgetTreeWidth 1000)}
%     {I configureEntry(widgetTreeDepth 1000)}
%     {I configureEntry(widgetShowStrings true)}
%     F =  {New Open.file init(name:"/ozdevel/scollar/scoll/simplecaretaker.scoll"
% 			     flags:[read])}
%     String = {F read(list: $ size:all)}
%  in
%     {F close}
%     {I inspect(try {ToKernel
% 		   {ScollParse String}
% 		   } catch Err then Err end)}
%  end
 
%  thread {Test} end

 
   fun{ScollRawTokenize Str} % return list of token
      Tp1#Chars1#Tkns#L#C =
      {List.foldR   % parsing backwards
       Str
       fun{$  El Type#Chars#Tokens#Line#Col}
	  ElType = case {Char.type El}
		   of lower then string
		   [] upper then string
		   [] digit then string
		   [] space then space
		   [] punct then if El == &. then string else punct end
		   [] other then raise 'invalid character type '(El line:Line col:Col) end  other
		   else raise 'invalid character type '(El line:Line col:Col) end other
		   end
	 NewLine NewCol 
       in
	  if El == &\n then NewLine=Line-1 NewCol=0 else NewLine=Line NewCol=Col-1  end
	  if ElType == Type
	  then case Type of punct
	       then case El|Chars
		    of "=>" then  ElType#(El|Chars)#Tokens#NewLine#NewCol
		    [] "*/" then ElType#(El|Chars)#Tokens#NewLine#NewCol
		    [] "/*" then  ElType#(El|Chars)#Tokens#NewLine#NewCol
		    else ElType#[El]#(tkn(chars:Chars type:Type line:Line col:Col)|Tokens)#NewLine#NewCol 
		    end
	       else ElType#(El|Chars)#Tokens#NewLine#NewCol 
	       end
	  else case Type
	       of space then %Spaces are thrown away
		  ElType#[El]#Tokens#NewLine#NewCol
	       else ElType#[El]#(tkn(chars:Chars type:Type line:Line col:Col)|Tokens)#NewLine#NewCol
	       end  
	  end
       end
       space#nil#nil#0#0}
   in
      if Tp1 == space then Tkns
      else tkn(chars:Chars1 type:Tp1 line:L col:C)|Tkns
      end
   end

   proc{CheckTokens Raw}
      for Token in Raw
      do case Token of tkn(chars:Chars type:punct line:_ col:_)
	 then if {Not {Member Chars
		       ["=>" "/*" "*/" "/" "(" ")" "{" "}" "_" ":" "?" ";" "!" "," "."]}}
	      then raise illegalToken({String.toAtom Chars} line:Token.line col:Token.col) end
	      end
	 else skip
	 end
      end
   end
  
 
   fun{ScollTokenize Str}
      Raw = {ScollRawTokenize Str}
   in
      {CheckTokens Raw}
      {RemoveComments Raw false 0 0 0 0}
   end
   
   fun{RemoveComments Tokens InComment FromLine FromCol ToLine ToCol} % no nested comments
      case InComment
      of false then case Tokens
		    of nil then nil
		    [] tkn(chars:"/*" type:punct line:L col:C)|Rest
		    then {RemoveComments Rest true L C L C}
		    else (Tokens.1)|{RemoveComments Tokens.2 false 0 0 0 0}

		    end
      [] true then case Tokens
		   of nil then raise 'comments not closed '(fromLine:FromLine fromCol:FromCol toLine:ToLine toCol:ToCol ) end nil
		   [] tkn(chars:"*/" type:punct line:L col:C)|Rest
		   then {RemoveComments Rest false L C L C }
		   else {RemoveComments Tokens.2 true FromLine FromCol Tokens.1.line Tokens.1.col}
		   end
      end
   end


   fun{ScollParse Str}
      Tokens = {ScollTokenize Str}
   in      program('declare':{ParseDeclare {FromTo Tokens "declare" "system"}}
		   system: {ParseSystem {FromTo Tokens "system" "behavior"}}
		   behavior:{ParseBehavior {FromTo {From Tokens "system"} "behavior" "subject"}}
		   subject:{ParseSubject {FromTo Tokens "subject" "config"}}
		   config:{ParseConfig {FromTo Tokens "config" "goal"}}
		   goal:{ParseGoal {From Tokens "goal"}})
   end
   
   fun{From Tokens Begin}
      {List.dropWhile Tokens fun{$ X} X.chars \= Begin end}
   end

   fun{FromTo Tokens Begin End}
      {List.takeWhile {From Tokens Begin} fun{$ X} X.chars \= End end}
   end

   fun{ParseDeclare Tokens}
      State =  {FromTo Tokens "state" "behavior"}
      Beh =  {FromTo Tokens "behavior" "knowledge"}
      Know = {FromTo Tokens "knowledge" "system"}
      {ForAll [State Beh Know] proc{$ Lst}
				 try Lst.2.1.chars=":"
				 catch _ then raise 'forgot colon in declare part'(line:Lst.2.1.line col:Lst.2.1.col) end
				 end
			      end}
   in 
      'declare'(state: {ParseDecl State.2.2}
		behavior: {ParseDecl Beh.2.2}
		knowledge:{ParseDecl Know.2.2})
   end

   fun{ParseSystem Tokens}
      case Tokens
      of nil then raise 'no system part' end
      [] tkn(chars:"system" type:string line:_ col:_)|Rules then {ParseRules Rules}
      else raise 'expected system part here '(line:Tokens.1.line col:Tokens.1.col) end nil
      end
   end

   fun{ParseRules Rules}
      Rule1 Body1 HeadPart Rest
   in
      case Rules
      of nil then nil
      else {List.takeDropWhile Rules
	    fun{$ Tkn} Tkn.type \= punct orelse Tkn.chars \=  ";"
	    end
	    Rule1 Rest}
	 case Rest 
	 of tkn(chars:";" type:punct line:_ col:_) | Rest2
	 then
	    {List.takeDropWhile Rule1
	     fun{$ Tkn} Tkn.type \= punct orelse Tkn.chars \= "=>"
	     end
	     Body1 HeadPart}
	    case HeadPart
	    of tkn(chars:"=>" type:punct line:_ col:_)|Head1
	    then rule(body: {ParseFacts Body1 "!"}
		      head: {ParseFacts Head1 "!"})|{ParseRules Rest2}
	    else
	       raise 'rule not properly separated into head and body '(fromLine: Rules.1.line fromCol:Rules.1.col
								      toLine: Rest.1.line toCol:Rest.1.col) end nil
	    end
	 else LastToken = {List.last Rules}
	 in
	    raise 'rule not ended by semicolon '(fromLine: Rules.1.line fromCol:Rules.1.col
						 toLine: LastToken.line toCol:LastToken.col)
	    end
	    nil
	 end
      end
   end

   fun{ParseBehavior Tokens}
      BehList =  case Tokens
		 of nil then raise 'no behavior part' end
		 [] tkn(chars:"behavior" type:string line:_ col:_)|Behaviors then {ParseBehaviors Behaviors}
		 else raise 'expected behavior part here '(line: Tokens.1.line col: Tokens.1.col) end nil
		 end
   in
      {List.toRecord '#' {Map BehList fun{$ Beh} (Beh.name)#Beh end}}
   end


   fun{ParseBehaviors Tokens}
      case Tokens of nil then nil
      else
	 Beh1 Rest in
	 {List.takeDropWhile Tokens
	  fun{$ Tkn} Tkn.type \= punct orelse Tkn.chars \= "}" 
	  end
	  Beh1 Rest}
	 case Beh1
	 of tkn(chars:BName type:string line:_ col:_)|tkn(chars:"{" type:punct line:_ col:_)|Rules
	 then case Rest
	      of tkn(chars:"}" type:punct line:_ col:_)|MoreBehaviors
	      then
		 behavior(name:{String.toAtom BName}
			  rules:{ParseRules Rules})|{ParseBehaviors MoreBehaviors}
	      else LastToken = {List.last Beh1}
	      in
		 raise 'behavior declaration not closed by curly bracket '(fromLine:Beh1.1.line fromCol:Beh1.1.col
									   toLine:LastToken.line toCol:LastToken.col)
		 end
		 nil
	      end
	 else raise 'behavior declaration not starting as expected '(line: Tokens.1.line col: Tokens.1.col) end nil
	 end
      end
   end
	 

   fun{ParseSubject Tokens}
      case Tokens
      of nil then raise 'no subject part' end
      [] tkn(chars:"subject" type:string line:_ col:_)|Subjects then {ParseSubjects Subjects}
      else raise 'expected subject part here '(line:Tokens.1.line col:Tokens.1.col) end nil
      end
   end

   fun{ParseSubjects Tokens} %subjects can be preceded by "?"
      S
   in
      case Tokens
      of nil then nil
      [] tkn(chars:SName type:string line:_ col:_)|tkn(chars:":" type:punct line:_ col:_)|tkn(chars:SType type:string line:_ col:_)|Rest
      then S = subject(name:{String.toAtom SName}
		       type:{String.toAtom SType}
		       query: false)
	 {Register S Tokens.1.line Tokens.1.col}
	 S|{ParseSubjects Rest}
      [] tkn(chars:"?" type:punct line:_ col:_)|tkn(chars:SName type:string line:_ col:_)|tkn(chars:":" type:punct line:_ col:_)|tkn(chars:SType type:string line:_ col:_)|Rest
      then S = subject(name:{String.toAtom SName}
		       type:{String.toAtom SType}
		       query: true)
	 {Register S Tokens.1.line Tokens.1.col}
	 S|{ParseSubjects Rest}
      else
	 raise 'no subject found when parsing subject '(line:Tokens.1.line col:Tokens.1.col) end nil
      end 
   end

   fun{ParseConfig Tokens}
      Facts  = case Tokens
	       of nil then raise 'no config part' end nil
	       [] tkn(chars:"config" type:string line:_ col:_)|Facts then {ParseFacts Facts "?"}
	       else raise 'expected  config part here '(line: Tokens.1.line col: Tokens.1.col) end nil
	       end
      Plain  Optional
   in
      {List.partition Facts
       fun{$ F} {HasFeature F 1} end
       Plain Optional}
      config(facts:Plain
	     optional:{Map Optional
		       fun{$ R}
			  if {Not {HasFeature R.fact 1}}
			  then raise 'double options in fact '(R) end
			  end
			  R.fact
		       end})
   end

   fun{ParseGoal Tokens}
      Goals =  case Tokens
	       of nil then raise 'no goal part' end
	       [] tkn(chars:"goal" type:string line:_ col:_)|GoalFacts then {ParseFacts GoalFacts "!"}
	       else raise 'expected goal part here '(line:Tokens.1.line col:Tokens.1.col) end nil
	       end
      Liv Saf
   in
      {List.partition Goals
       fun{$ F} {HasFeature F 1} end
       Liv Saf}
      goal(liv:Liv
	   saf:{Map Saf
		fun{$ R}
		   if {Not {HasFeature R.fact 1}}
		   then raise 'double options in fact '({FindLocations R}) end
		   end
		   R.fact
		end})
   end
   
   fun{ParseFacts Tokens Opt} %facts can be preceded by Opt
      case Tokens
      of nil then nil
      else  F R in
	 {ParseFact Tokens Opt F R}
	 if F==nil then nil else F|{ParseFacts R Opt} end
      end
   end
  
   proc{ParseFact Tokens Opt ?Fact ?Remaining} %facts can be preceded by Opt string
      case Tokens
      of nil then Fact=nil Remaining=nil
      [] tkn(chars:CharsSubj type:string line:L1 col:C1)|tkn(chars:":" type:punct line:_ col:_)
	 |tkn(chars:CharsPred type:string line:_ col:_)|tkn(chars:"(" type:punct line:_ col:_)
	 |tkn(chars:")" type:punct line:L2 col:C2)|Rest
      then {ParseFactArgs CharsPred
	    tkn(chars:CharsSubj type:string line:L1 col:C1)|tkn(chars:")" type:punct line:L2 col:C2)|Rest
	    Fact Remaining}
	 {Register Fact L1 C1}
      [] tkn(chars:CharsSubj type:string line:L1 col:C1)|tkn(chars:":" type:punct line:_ col:_)
	 |tkn(chars:CharsPred type:string line:_ col:_)|tkn(chars:"(" type:punct line:L2 col:C2)|Rest
      then {ParseFactArgs CharsPred
	    tkn(chars:CharsSubj type:string line:L1 col:C1)|tkn(chars:"," type:punct line:L2 col:C2)|Rest
	    Fact Remaining}
	 {Register Fact L1 C1}
      [] tkn(chars:Chars type:string line:L1 col:C1)|tkn(chars:"(" type:punct line:_ col:_)|Rest
      then {ParseFactArgs Chars Rest Fact Remaining}
	 {Register Fact L1 C1}
      [] tkn(chars:!Opt type:punct line:L1 col:C1 )|Rest
      then ActFact in
	 {ParseFact Rest Opt ActFact Remaining}
	 Fact =  optFact(option: {String.toAtom Opt}
			 fact: ActFact)
	 {Register Fact L1 C1}
      else Remaining = nil  Fact=nil
	 raise 'no start of fact found when parsing fact '(Tokens.1 line:Tokens.1.line col:Tokens.1.col) end
      end 
   end

   local
      Entities = {NewDictionary}
      %Lines = {New Dictionary}
   in
      proc{Register Entity Line Col}
	 R = r(entity:Entity line:Line col:Col)
	 OldVal
      in
	 {Dictionary.condExchange Entities {Label Entity} nil OldVal R|OldVal}
	 %{Dictionary.condExchange Lines Location.line nil OldVal R|OldVal}
      end
      fun{FindLocations Entity}
	 locations(entity:Entity
		   1: {Map {Filter {Dictionary.condGet Entities {Label Entity} [r(entity:Entity line:0 col:0)]}
			    fun{$ V} V.entity == Entity end}
		       fun{$ V} loc(line:V.line col:V.col) end})
      end
   end
   
   proc{ParseFactArgs LblStr Tokens ?Fact ?Remaining}
      Args Rest
      Lbl = {String.toAtom LblStr}
   in
      {List.takeDropWhile Tokens
       fun{$ Tkn} Tkn.type==string orelse Tkn.chars=="_" orelse Tkn.chars=="," end
       Args Rest}
      case Rest
      of tkn(chars:")" type:punct line:_ col:_)|Rest3 then
	 Remaining = Rest3
	 Fact = {List.toTuple Lbl {Map {RemoveCommaSeparation Args} fun{$ Tkn} {String.toAtom Tkn.chars} end}}
      else  Remaining = nil  Fact=nil
	 raise 'no closing bracket found when parsing fact '(line:Tokens.1.line col:Tokens.1.col) end
      end
   end
   

   fun{RemoveCommaSeparation Args}
      LastToken 
   in
      if Args == nil then nil
      else
	 LastToken = {List.last Args}
	 if {IsEven {Length Args}}
	 then
	    raise 'no proper comma separated arguments when parsing '(fromLine: Args.1.line fromCol: Args.1.col
								      toLine: LastToken.line toCol: LastToken.col)
	    end
	    nil
	 else
	    {List.filterInd Args
	     fun{$ I Arg}  if {IsOdd I} andthen (Arg.type==string orelse Arg.chars=="_") then true
			   elseif {IsEven I} andthen Arg.chars=="," then false
			   else raise 'no comma separated arguments when parsing '(fromLine: Args.1.line fromCol: Args.1.col
										   toLine: LastToken.line toCol: LastToken.col)
				end
			      false
			   end
	     end}
	 end
      end
   end
   
	 
   fun{ParseDecl Tokens}
      P
   in
      case Tokens
      of nil then nil
      [] tkn(chars: Lbl type:string line:_ col:_)|tkn(chars: "/" type:punct line:_ col:_)|tkn(chars: Arity type:string line:_ col:_)|Rest
      then P =  pred(label:{String.toAtom Lbl}
		     arity:{StringToInt Arity})
	 {Register P  Tokens.1.line Tokens.1.col}
	 P|{ParseDecl Rest}
      else raise 'bad predicate declaration '(line:Tokens.1.line col:Tokens.1.col) end nil
      end
   end
 
   
   fun{ToHorn Program}  % multiheaded rules => HORN clauses
      {Record.adjoin Program
       program(behavior: {Record.map Program.behavior
			  fun{$ Beh} {Record.adjoin Beh
				      behavior(rules: {Flatten
						       {Map Beh.rules
							fun{$ Rule} {Map Rule.head
								     fun{$ Head} {Record.adjoin Rule
										  rule(head: Head)}
								     end}
							end}
						      })
				     }
			  end}
	       system: {Flatten {Map Program.system
				 fun{$ Rule} {Map Rule.head
					      fun{$ Head} {Record.adjoin Rule
							   rule(head: Head)}
					      end}
				 end}})
       
      }
   end
   
   fun{LocalArities Program BehaviorHornClauses Globals}
      BodyPreds =  {Flatten {Map BehaviorHornClauses
			     fun{$ Rule}  Rule.body 
			     end}}
      HeadPreds =  {Filter {Map BehaviorHornClauses
			    fun{$ Rule} Rule.head
			    end}
		    fun{$ H} H \= nil end}
      LocalPreds = {Filter {Append HeadPreds BodyPreds}
		    fun{$ Pr} {Not{HasFeature Globals {Label Pr}}}
		    end}
      fun{CheckArity Pred}
	 Lbl = {Label Pred}
	 Ar = {Width Pred} +1
      in
	 {Not {HasFeature Globals Lbl}} orelse  Globals.Lbl.arity == Ar
      end

      fun{CheckLocals Lst Rec}
	 case Lst
	 of nil then Rec
	 [] Pred|Rest
	 then Lbl={Label Pred} in
	    if {HasFeature Rec Lbl}
	    then if {Not {Width Pred}+1 == Rec.Lbl}
		 then raise 'local predicate used with wrong arity '({FindLocations Pred}) end
		 end
	       {CheckLocals Rest Rec}
	    else {CheckLocals Rest {Record.adjoin Rec {List.toRecord '#' [Lbl#({Width Pred}+1)]}}}
	    end
	 end
      end
   in
      {ForAll {Flatten [HeadPreds
			BodyPreds
		       ]} proc{$ Pred} if {Not {CheckArity Pred}}
				       then raise 'arity mismatch '({FindLocations Pred}) end
				       end
			  end}
      {CheckLocals LocalPreds nil}
   end
   
			   
   fun{AddArities KernelProgram} % check arities and rule types
      GlobalAritiesAndTypes = {List.toRecord '#'
			       {Flatten
				{Record.toList
				 {Record.mapInd KernelProgram.'declare'
				  fun{$ Tp Lst}
				     {Map Lst
				      fun{$ Decl} (Decl.label)#(r(arity:Decl.arity type:Tp))
				      end}
				  end}}}}
      BehaviorWithArities = {Record.map KernelProgram.behavior
			     fun{$ Beh} {Record.adjoin Beh
					 behavior(predicates: {LocalArities KernelProgram
							       Beh.rules GlobalAritiesAndTypes})}
			     end}
   in
      {Record.adjoin KernelProgram program(predicates:GlobalAritiesAndTypes
					   behavior:BehaviorWithArities)}
   end


   fun{AddRefinements KernelProgram} % add refinement relations for behavior only (maybe later for knowledge also)
      {Record.adjoin
       KernelProgram
       program(behaviorRefinements: {Flatten
				     {Map {Filter KernelProgram.system
					   fun{$ Rule} {Some KernelProgram.'declare'.behavior
							fun{$ Decl} Decl.label == {Label Rule.head} end}
					   end}
				      fun{$ RefRule} {Map RefRule.body
						      fun{$ Pr} ref(coarse: Pr
								    fine: RefRule.head)
						      end}
				      end}}
	      )}
   end
   
   fun  {CreateUnderBars}
      Cnt = {NewCell 1}
   in
      fun{$} Old New in
	 {Exchange Cnt Old New}
	 New = Old+1
	 {VirtualString.toAtom '_'#Old}
      end
   end
   
   fun{DeUnderBarPreds PredList NextUnderBar}
      {Map PredList
       fun{$ Pred}
	  {Record.map
	   Pred
	   fun{$ X} case X of '_' then {NextUnderBar}
		    else X
		    end
	   end}
       end}
   end
   
   fun{DeUnderBar HornProg}
      {Record.adjoin
       HornProg
       program(system: {Map HornProg.system
			fun{$ Rule}
			   HeadAndBody = {DeUnderBarPreds Rule.head|Rule.body {CreateUnderBars}}
			in {Record.adjoin Rule
			    rule(head:HeadAndBody.1
				 body:HeadAndBody.2)}
			end}
	       behavior: {Record.map  HornProg.behavior
			  fun{$ Beh} {Record.adjoin
				      Beh
				      behavior(rules:{Map Beh.rules
						      fun{$ Rule}
							 HeadAndBody = {DeUnderBarPreds Rule.head|Rule.body {CreateUnderBars}}
						      in {Record.adjoin Rule
							  rule(head:HeadAndBody.1
							       body:HeadAndBody.2)}
						      end}
					      )}
			  end}
	      )}
   end
   
   fun{ToKernel Program}
      KP = {AddRefinements {AddArities {DeUnderBar {ToHorn Program}}}}
   in
      {Analyze KP}
      KP
   end


%    fun{TokensToVS Tokens}
%       if {IsList Tokens}
%       then {Map Tokens fun{$ Tkn} {Record.adjoin Tkn tkn(chars:{String.toAtom Tkn.chars})}
% 		       end}
%       else Tokens
%       end
%    end

   proc{AnalyzeFactForSubjectExistance KP Part Fact}
      for Name in {Record.toList Fact}
      do if {Not {Some KP.subject fun{$ Subj} Subj.name == Name end}}
	 then raise 'undeclared subject used in '(Part {FindLocations Fact}) end
	 end
      end
   end

   proc{AnalyzeNoBehaviorFact KP Part Fact}
      Lbl = {Label Fact}
      {AnalyzeFactForSubjectExistance KP Part Fact}
      Subj = {Filter KP.subject fun{$ S} S.name == Fact.1 end}.1
      Beh = KP.behavior.(Subj.type)
   in
      if {HasFeature KP.predicates Lbl}
      then
	 if KP.predicates.Lbl.type == behavior then raise 'behavior facts not alowed in part '(Part {FindLocations Fact}) end end
	 if {Width Fact} \= KP.predicates.Lbl.arity then raise 'arity mismatch in part '(Part {FindLocations Fact}) end end
      elseif {HasFeature Beh.predicates Lbl}
      then if {Width Fact} \= Beh.predicates.Lbl then raise 'arity mismatch in part'(Part {FindLocations Fact}) end end
      else raise 'undeclared predicate used in part '(Part {FindLocations Fact}) end
      end
   end

   proc{AnalyzeSystemRules KP}
      for Rule in KP.system
      do for Pred in (Rule.head)|Rule.body
	 do Lbl = {Label Pred}
	 in
	    if {Not {HasFeature KP.predicates Lbl}}
	    then raise predicateNotDeclaredInSystemRule({FindLocations Pred}) end
	    elseif {Not KP.predicates.Lbl.arity == {Width Pred}}
	    then raise predicateUsedWithWrongArityInSystemRule({FindLocations Pred}) end
	    end
	 end
      end
   end 
      
   proc{Analyze KP} %labels and arities of system rule preds and behavior rule preds have been checked
      %behavior uniqueness is already checked
      %subject uniqueness and valid behavior
      {AnalyzeSystemRules KP}
      for Subj in KP.subject
      do if {Length {Filter KP.subject fun{$ S} S.name == Subj.name end}} > 1
	 then raise 'duplicate subject declared '(Subj.name {FindLocations Subj}) end
	 end
	 if {Not {HasFeature KP.behavior Subj.type}}
	 then raise 'subject type not declared '(Subj.name {FindLocations Subj}) end
	 end
      end
      %subjects, labels, arities and types of goal facts
      for Fact in {Append KP.goal.liv KP.goal.saf}
      do  {AnalyzeNoBehaviorFact KP goal Fact}      
      end
      %subjects, labels arities and types of config facts
      for Fact in {Append KP.config.facts KP.config.optional}
      do  {AnalyzeNoBehaviorFact KP config Fact}
      end
   end
end
