functor
import
   Open FD Space OS % Application
   System(show:Show showInfo:ShowInfo)
   Property
   DotGraph at 'dotgraph.ozf'
   ScollParser(scollParse:ScollParse toKernel:ToKernel) at 'scollparser.ozf'
   ScollarSearch at 'scollarSearch.ozf'
   Inspector(inspect:Inspect)
   %ScollarProgress(newBar:NewBar) at 'scollarProgress.ozf'
define
   %DataDir = '/ozdevel/scollar/data/'
   \insert scollarcore.oz
   %\insert scollparser.oz
   \insert scollarReply.oz
   %\insert administer.oz
   
   {Property.put errors errors(debug:true depth:20 width:20)}
   {Property.put 'print.depth' 20}
   {Property.put 'print.width' 20}

   SolutionsCell = {NewCell empty}
   FixptCell = {NewCell empty}
   ProblemCell = {NewCell empty}
   
   %16 colors as default
   DefaultDotColors = colors(black green blue salmon darkviolet red steelblue darkkhaki seagreen orange violetred navy yellow cyan indigo magenta)
   fun{DotColorsFor ListOfBinaryPredLabels}
      Nmbr = {Width DefaultDotColors}
   in
      {MapInd ListOfBinaryPredLabels fun{$ I _} if I =< Nmbr then DefaultDotColors.I else gray end
				     end}
   end
   fun{GetBinaryStates ParsedPattern} % returnlist of labels of binary state predicates in ParsedPattern
      {Map {Filter ParsedPattern.'declare'.state
	    fun{$ Prd} Prd.arity == 2 end}
       fun{$ Prd} Prd.label end}
   end

   
   proc{ParsePattern Pattern ?Problem ?Message ?OK}
      %if Options.debug then {Show inParsePattern} end
      Prog 
   in
      try Prog  = {VirtualString.toString Pattern}
	 Problem = {ToKernel {ScollParse Prog}}  % should still be checked for grammar.
	 ProblemCell := Problem
	 %{Inspect Problem}
	 %Message = nil
	 OK = true
	 % {Inspect Problem}
      catch Msg then
	 %Problem = nil
	 Message = Msg
	 OK = false
      end
   end
   
   fun{CheckSyntax Pattern}
      Message
   in
      if {ParsePattern Pattern ?_ ?Message}
      %if {ParsePattern Pattern {Inspect} ?Message}
      then "<reply><check>\nOK\n</reply>\n"
      else {Flatten ["<error>\n"
		     {ErrorMsg Message}
		     "\n</error>\n"]}
      end
   end
   
   fun{ErrorMsg E}
      if {String.is E} then E
      elseif {VirtualString.is E} then {VirtualString.toString E}
      else {Value.toVirtualString E 100 100}
      end
   end
      
   proc{Process RequestAndData}% TimeOut}   % !!! CODE VULNERABLE FOR WINDOWS AND MAC LINE ENDINGS??
      % RequestAndData: first line contains request and options, all separated by a single space
      %                 following lines contain data argument
      % example: "sols 1 10000\ndeclare ..... 
      Request Data Arguments 
   in
      {String.token RequestAndData &\n Request Data}
      %{Inspect RequestAndData}
      Arguments = {String.tokens Request & }
      case Arguments
      of ["check"] then {ReplyResult {CheckSyntax Data}}
      [] ["status"] then skip % status is given automatically
      [] ["fixpts"] then
	 FixptCell := fixpoints(min:nil max:nil)
	 {ReplyResult {FixPts Data}}
      [] ["sol1" TO]  then
	 if {String.isInt TO} % Arguments = ["sol1" RecomputationDistance TimeOutInMillisec]
	 then
	    SolutionsCell := empty
	    {ReplyResult {Solve one Data {String.toInt TO}}}
	 else
	    {ReplyResult {ErrorMsg "expected integer arguments RecomputationDistance and TimeOutInMillisec"}}
	 end
      [] ["sols" TO]  then
	 if {String.isInt TO} % Arguments = ["sol1" RecomputationDistance TimeOutInMillisec]
	 then
	    SolutionsCell := empty
	    {ReplyResult {Solve all Data  {String.toInt TO}}}
	 else
	    {ReplyResult {ErrorMsg "expected integer arguments RecomputationDistance and TimeOutInMillisec"}}
	 end
      [] ["show" SolutionNumber] then if {String.isInt SolutionNumber}
				      then {ReplyResult  {ShowSolution {String.toInt SolutionNumber}}}
				      else {ReplyResult  {ErrorMsg "expected integer argument SolutionNumber"}}
				      end
      else {ReplyResult {ErrorMsg "unknown action requested"}}
      end
   end

   
%    fun{ProcessControl ControlMsg}
%       {ShowInfo 'inProcessControl'}
%       @InterruptCell=unit
%       "message arrived in Oz process OK\n"
%    end

   fun{FixPts Pattern}
      Problem ParserMsg
   in
      if {ParsePattern Pattern ?Problem ?ParserMsg} == false
      then  {ErrorMsg ParserMsg}
      else
	 MinFp MaxFp Err
      in
	 try {CalculateFixpoints Problem MinFp MaxFp} 
	 catch E then {Inspect E}
	    Err = E
	    try MinFp = nil catch _ then skip end
	    try MaxFp = nil catch _ then skip end
	 end
	 if MinFp \= nil andthen MaxFp \= nil then FixptCell := fixpoints(min:MinFp max:MaxFp) end
 	 %{Inspect @FixptCell}
	 if {IsDet Err} then
	    {ErrorMsg 'fixpoint calculation went wrong'(Err)}
	 else try
		 ArcLabels = {GetBinaryStates Problem}
	      in
		 {FixpointsReply MinFp MaxFp ArcLabels {DotColorsFor ArcLabels}}
	      catch E then
		 {ErrorMsg 'trouble marshalling calculated fixpoint'(E)}
	      end
	 end
      end				   
   end					   

   
   fun{Solve OneOrAll Pattern TimeOut}
      Problem ParserMsg Response
   in
      if {ParsePattern Pattern ?Problem ?ParserMsg} == false
      then Response = {ErrorMsg ParserMsg}
      else
	 TimeTaken All Good Completed
	 Time1 = {OS.time}
      in
	 try
	    {ShowInfo  "trying to initiate progress"}
	    InterruptCell := _
	    {ResetSolCnt}
	    % ProgressBarCell := {NewBar @InterruptCell}
	    %{ShowInfo  "initiated progress bar"}
	    {CalculateSolutions
	     Problem OneOrAll Time1 TimeOut TimeTaken All Good Completed}
	    SolutionsCell := Good
	    %{Inspect SolutionsCell}
	    %{Inspect Good}
	    %if {IsDet Completed} then {Show 'Completed is det'} else {Show 'Completed is NOT det'} end
	 catch E then Response = {ErrorMsg 'could not calculate solution(s). Problem may have invalid format'(E)}
	 end
	 if {Not {IsDet Response}}
	 then  Response = try
			     ArcLabels = {GetBinaryStates Problem}
			  in
			     {SolutionsReply TimeTaken {List.length All} Good Completed ArcLabels {DotColorsFor ArcLabels} }
			  catch E then {ErrorMsg 'trouble marshalling solution(s)'#(E)}
			  end
	 end
	 %{ReportProgress {Pow 2 ProgressReportDepth}}
	 %if {Not @ProgressBarCell == nil} then {@ProgressBarCell setRatio(64 64)} end
	 %ProgressBarCell := nil
      end
      %{ShowInfo Response}
      %@EndOfControlSignalCell=unit
      Response
   end

   fun{ShowSolution I}
      if @SolutionsCell == empty orelse {List.length @SolutionsCell} < I
      then 
	 {ErrorMsg "was asked to show non-existing solution "#I}
      else
	 ArcLabels = {GetBinaryStates @ProblemCell}
      in
	 {ShowSolutionReply I @SolutionsCell ArcLabels {DotColorsFor ArcLabels}}
      end
   end
   
   proc{ServeRequest}
      Request
      L
      %Reply
   in
      Request = {ServerSocket read(list:$
				   size:4096
				   len:L)}
      {Show 'Length Request'(L)}
      {Wait Request}
      {Process Request}
%       if Reply == endOfCommunication
%       then
% 	 {RequestsSocket close}
%       else {ReplyResult Reply}
%       end
   end


   proc{ServeControl} % only incoming
      ControlMsg
      L
   in
      ControlMsg = {ControlSocket read(list:$
				       size:4096
				       len:L)}
      {Show 'Length Control Msg'(L)}
      {Wait ControlMsg}
      if ControlMsg == "interrupt\n" then @InterruptCell = unit end
      if ControlMsg \= "endOfControl\n" then {ServeControl} end
   end


%     proc{ServeControl ControlSocket} % asynchronous communication: possible replies should go via global ControlReportPort
%        L
%        ControlMsg 
%        ControlReply
%     in
%        ControlMsg = {ControlSocket read(list:$
%  				       size:4096
%  				       len:L)}
%        {Show 'Length Control Message'(L)}
%        %{ControlSocket flush}
%        %{ShowInfo 'control socket flushed'}
%        case {Record.waitOr r(@EndOfControlSignalCell ControlMsg)}
%        of 1 then {ShowInfo 'end-of-control-signal received'}
%  	 skip % no more control msgs to be expected for current calculation
%        [] 2 then
%  	 thread {ShowInfo 'will proces control msg now'}
%  	    ControlReply = {ProcessControl ControlMsg}
%  	    {ShowInfo 'control msg processed'}
%  	 end
%  	 case {Record.waitOr r(@EndOfControlSignalCell ControlReply)}
%  	 of 1 then {ShowInfo 'End-Of-Control-Signal received (2)'}
%  	    skip % new calculation overrides control msg currently being processed
%  	 [] 2 then
%  	    {ShowInfo 'now ready for next control signal'}
%  	    {Port.send ControlReportPort ControlReply}
%  	    {ServeControl ControlSocket}
%  	 end
%        end
%     end

 %    proc {StartControlReportPort ControlSocket}
%        thread
%  	 for Msg in ControlReportStream
%  	 do
%  	    {ControlSocket write(vs:Msg)} % java side uses socket.readLine()
%  	    {ShowInfo "control message \""#Msg#"\" was sent on control socket"}
%  	    %{ControlSocket flush}
%  	 end
%        end
%     end
   
  % ProgressBarCell = {NewCell nil}
   InterruptCell = {NewCell _}
   ServerSocket     ControlSocket
   ServerPortNumber ControlPortNumber
   ReplyStatus
   ReplyResult
   ResetSolCnt
   AddSolCnt
in   
   local S P = {NewPort S}
      SolCnt = {NewCell 0}
   in
      thread
	 for Msg in S do
	    case Msg
	    of result#Vs then
	       {ServerSocket write(vs:Vs)}
	       {ServerSocket flush}
	       {ServeRequest}
	    [] status#Vs then
	       {ServerSocket write(vs:"<reply><status>\n"#{VirtualString.toString Vs}#"\n</reply>\n")}
	       {ServerSocket flush}
	    [] resetSolCnt then
	       SolCnt := 0
	    [] addSolCnt then
	       Str =  {VirtualString.toString (@SolCnt+1)#" solution"#if @SolCnt==0 then "" else "s" end#" found"}
	    in
	       SolCnt := @SolCnt + 1
	       {ServerSocket write(vs:"<reply><status>\n"#Str#"\n</reply>\n")}
	       {ServerSocket flush}
	    end
	 end
      end
      proc{ReplyStatus Vs}
	 {Port.send P status#Vs}
      end
      proc{ReplyResult Vs}
	 {Port.send P result#Vs}
      end
      proc{ResetSolCnt}
	 {Port.send P resetSolCnt}
      end
      proc{AddSolCnt}
	 {Port.send P addSolCnt}
      end
   end
   ServerSocket={New Open.socket init}
   ServerPortNumber={ServerSocket bind(port:$)}
   {ServerSocket listen}
   ControlSocket={New Open.socket init}
   ControlPortNumber={ControlSocket bind(port:$)}
   {ControlSocket listen}
   {New Open.pipe
    init(cmd: "java"
	 args: ["-jar" "swingscollar.jar" ServerPortNumber ControlPortNumber]
	 pid:  _)
    _ /*JavaGui*/}
   {ServerSocket accept(host: _/*H*/ port:_/*P*/)}
   {ControlSocket accept(host: _/*H*/ port:_/*P*/)}
   thread {ServeControl} end
   {ServeRequest} 
   %{Application.exit 1}
end