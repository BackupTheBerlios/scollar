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
functor
import
   Open FD Space OS Application
   System(show:Show showInfo:ShowInfo)
   Property
   DotGraph at 'dotgraph.ozf'
   ScollParser(scollParse:ScollParse toKernel:ToKernel) at 'scollparser.ozf'
   ScollarSearch at 'scollarSearch.ozf'
   Inspector(inspect:Inspect)
   
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
   fun{GetBinaryPermissions ParsedPattern} % returnlist of labels of binary permissions predicates in ParsedPattern
      {Map {Filter ParsedPattern.'declare'.permission
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
	 {Inspect Problem}
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
      then "<reply>\nOK\n</reply>\n"
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
      
   fun{Process RequestAndData}% TimeOut}   % !!! CODE VULNERABLE FOR WINDOWS AND MAC LINE ENDINGS??
      % RequestAndData: first line contains request and options, all separated by a single space
      %                 following lines contain data argument
      % example: "sols 1 10000\ndeclare ..... 
      Request Data Arguments 
   in
      {String.token RequestAndData &\n Request Data}
      %{Inspect RequestAndData}
      Arguments = {String.tokens Request & }
      case Arguments
      of ["check"] then {CheckSyntax Data}
      [] ["fixpts"] then
	 FixptCell := fixpoints(min:nil max:nil)
	 {FixPts Data}
      [] ["sol1" RD TO]  then if {String.isInt RD} andthen {String.isInt TO} % Arguments = ["sol1" RecomputationDistance TimeOutInMillisec]
			      then
				 SolutionsCell := empty
				 {Solve one Data {String.toInt RD} {String.toInt TO}}
			      else {ErrorMsg "expected integer arguments RecomputationDistance and TimeOutInMillisec"}
			      end
      [] ["sols" RD TO]  then if {String.isInt RD} andthen {String.isInt TO} % Arguments = ["sol1" RecomputationDistance TimeOutInMillisec]
			      then
				 SolutionsCell := empty
				 {Solve all Data {String.toInt RD} {String.toInt TO}}
			      else {ErrorMsg "expected integer arguments RecomputationDistance and TimeOutInMillisec"}
			      end
      [] ["show" SolutionNumber] then if {String.isInt SolutionNumber}
			 then {ShowSolution {String.toInt SolutionNumber}}
			 else {ErrorMsg "expected integer argument SolutionNumber"}
		      end
      else {ErrorMsg "unknown action requested"}
      end
   end

   
   fun{ProcessControl ControlMsg}
      "contol ok \n"
   end

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
		 ArcLabels = {GetBinaryPermissions Problem}
	      in
		 {FixpointsReply MinFp MaxFp ArcLabels {DotColorsFor ArcLabels}}
	      catch E then
		 {ErrorMsg 'trouble marshalling calculated fixpoint'(E)}
	      end
	 end
      end				   
   end					   

   
   fun{Solve OneOrAll Pattern CalcDist TimeOut }
      Problem ParserMsg Response
   in
      if {ParsePattern Pattern ?Problem ?ParserMsg} == false
      then Response = {ErrorMsg ParserMsg}
      else
	 TimeTaken All Good Completed
	 Time1 = {OS.time}
      in
	 try {CalculateSolutions
	      Problem OneOrAll CalcDist Time1 TimeOut TimeTaken All Good Completed}
	    %{ShowInfo "CalculatingSolutionsInterop done"}
	    SolutionsCell := Good
	    %{Inspect SolutionsCell}
	    %{Inspect Good}
	    %if {IsDet Completed} then {Show 'Completed is det'} else {Show 'Completed is NOT det'} end
	 catch E then Response = {ErrorMsg 'could not calculate solution(s). Problem may have invalid format'(E)}
	 end
	 if {Not {IsDet Response}}
	 then  Response = try
			     ArcLabels = {GetBinaryPermissions Problem}
			  in
			     {SolutionsReply TimeTaken {List.length All} Good Completed ArcLabels {DotColorsFor ArcLabels} }
			  catch E then {ErrorMsg 'trouble marshalling solution(s)'#(E)}
			  end
	 end
      end
      %{ShowInfo Response}
      Response
   end

   fun{ShowSolution I}
      if @SolutionsCell == empty orelse {List.length @SolutionsCell} < I
      then 
	 {ErrorMsg "was asked to show non-existing solution "#I}
      else
	 ArcLabels = {GetBinaryPermissions @ProblemCell}
      in
	 {ShowSolutionReply I @SolutionsCell ArcLabels {DotColorsFor ArcLabels}}
      end
   end
   
   proc{ServeRequestsAndControl RequestsSocket ControlSocket} % synchronous communication: receive + reply
     %  {RequestsSocket flush} % fs added for testing 3 maart 2008
      Request
      L
      Reply
      ControlSignal
   in
      Request = {RequestsSocket read(list:$
				     size:4096
				     len:L)}
      {Show 'Length Request'(L)}
      {RequestsSocket flush}
      {Wait Request}
      thread {ServeControl ControlSocket ControlSignal} end
      Reply = {Process Request}
      ControlSignal=unit % stop calculation control, reply is ready
      if Reply == endOfCommunication
      then
	 {RequestsSocket close}
	 {ControlSocket close}
      else {RequestsSocket write(vs:Reply)} % java side uses socket.readLine()
	 {RequestsSocket flush}
	 {ServeRequestsAndControl RequestsSocket ControlSocket}
      end
   end


   proc{ServeControl ControlSocket EndOfControlSignal} % synchronous communication: receive + reply
      L
      ControlMsg 
      ControlReply
   in
      ControlMsg = {ControlSocket read(list:$
				       size:4096
				       len:L)}
      {Show 'Length Control Message'(L)}
      {ControlSocket flush}
      case {Record.waitOr r(EndOfControlSignal ControlMsg)}
      of 1 then skip % no more control msgs to be expected for current calculation
      [] 2 then
	 thread ControlReply = {ProcessControl ControlMsg} end
	 case {Record.waitOr r(EndOfControlSignal ControlReply)}
	 of 1 then skip % new calculation overrides control msg currently being processed
	 [] 2 then 
	    {ControlSocket write(vs:ControlReply)} % java side uses socket.readLine()
	    {ControlSocket flush}
	    {ServeControl ControlSocket EndOfControlSignal}
	 end
      end
   end

   ServerSocket
   ServerPort
   ControlSocket
   ControlPort
   %JarLocation = {Append {OS.dir} "swingscollar.jar"}
in
   ServerSocket={New Open.socket init}
   ServerPort={ServerSocket bind(port:$)}
   {ServerSocket listen}
   ControlSocket={New Open.socket init}
   ControlPort={ControlSocket bind(port:$)}
   {ControlSocket listen}
   {New Open.pipe
    init(cmd: "java"
	 args: ["-jar" "swingscollar.jar" ServerPort ControlPort]  
	 pid:  _)
    _ /*JavaGui*/}
   {ServerSocket accept(host: _/*H*/ port:_/*P*/)}
   {ControlSocket accept(host: _/*H*/ port:_/*P*/)}
   {ServeRequestsAndControl ServerSocket ControlSocket}
   {Application.exit 1}
end