%%%%%%%%%%%%
%
% ScollarSearch provides a class Object whose instances forward to Search.object
%
%%%%%%%%%%%%%
functor
import Space Search %Inspector(inspect:Inspect)
export Object 
define
   class Object
      attr
	 searchObject
	 undistributedSpace
	 finalize
	 learnFromFixpoints
	 minFixpt
	 maxFixpt
	 minimalOK
	 fixpointsFinished
	 
      meth script(PreScriptP MakeMinFixptP MakeMaxFixptP LearnFromFixpointsP DistributeP FinalizeP NextP)
	 fixpointsFinished := _
	 minFixpt := nil
	 maxFixpt := nil
	 finalize := FinalizeP
	 minimalOK := _
	 learnFromFixpoints := LearnFromFixpointsP
	 {self makeFixpoints(PreScriptP MakeMinFixptP MakeMaxFixptP)}
	 {Wait @fixpointsFinished}
	 %{Inspect minimalOK#(@minimalOK)}
	 if @minimalOK then
	    searchObject := {New Search.object
			     script(proc{$ Root}
				       {PreScriptP Root}
				       {LearnFromFixpointsP @minFixpt @maxFixpt Root}
				       {DistributeP Root}
				    end
				    NextP
				    rcd: 0)}
	 end
      end

      meth next($)
	 if @minimalOK then
	    Sp = {@searchObject nextS($)}
	 in
	    if Sp \= nil then
	       Sol = {Space.merge Sp.1}
	       %{Inspect unfinalizedSolution#Sol} 
	       C = {Space.clone @undistributedSpace}
	       {Space.inject C proc{$ Root}
				  {@learnFromFixpoints @minFixpt @maxFixpt Root}
				  {@finalize Sol Root}
			       end}
	       Status = {Space.ask C}
	    in
	       case Status
	       of succeeded then finalized({Space.merge C})
	       else {List.toTuple Status [1#Sol]}  
	       end
	    else nil
	    end
	 else
	    nil
	 end
      end
      
      meth makeFixpoints(PreP MinP MaxP)
	 MinSpace 
	 MaxSpace
      in
	 %{Inspect inMakeFixpoints}
	 undistributedSpace := {Space.new PreP}
	 if {Space.ask @undistributedSpace} \= succeeded then
	    @minimalOK = false
	    raise preSpaceNotSucceededInMakeFixpoints end
	 end
	 %{Inspect inMakeFixpointsAfterPreP}
	 MinSpace =  {Space.clone @undistributedSpace}
	 {Space.inject MinSpace MinP}
	 if {Space.ask MinSpace} \= succeeded then
	    @minimalOK = false
	    raise minFixpointSpaceNotSucceededInMakeFixpoints end
	 end
	 %{Inspect inMakeFixpointsAfterMinP}
	 MaxSpace =  {Space.clone MinSpace}
	 minFixpt := {Space.merge MinSpace}
	 {Space.inject MaxSpace MaxP}
	 if {Space.ask MaxSpace} \= succeeded then
	    @minimalOK = false
	    raise maxFixpointSpaceNotSucceededInMakeFixpoints end
	 end
	 %{Inspect inMakeFixpointsAfterMaxP}
	 maxFixpt := {Space.merge MaxSpace}
	 if {Not {IsDet @minimalOK}} then @minimalOK = true end
	 %{Inspect minimalOK#(@minimalOK)}
	 %{Inspect minFixpt#(@minFixpt)}
	 %{Inspect maxFixpt#(@maxFixpt)}
	 @fixpointsFinished = unit
      end

      meth getMinFixpt($)
	 {Wait @fixpointsFinished}
	 @minFixpt
      end

      meth getMaxFixpt($)
	 {Wait @fixpointsFinished}
	 @maxFixpt
      end

      
	    
      
   end
end
							   
