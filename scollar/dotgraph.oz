%%%%%%%%%%%%%%%%%%
%% Copyright  Fred Spiessens fredspiessens@skynet.be fred@evoluware.eu
%% write dot-files from graph structures
%% USE:
%% GW = {New DotGraphWrapper init(nodeIds: NodeIdList
%%                                edgeLabels: LabelList
%%                                colors: ColorList
%%                                getNode: NodeFunction
%%                                getArc: ArcFuntion return list of arcs)}
%% NodeIdList is a list of nodeId's (atoms or integers)
%% NodeFunction should take a node id and return a record:
%%       node(label:VS % obligatory
%%            fontcolor:VS ... optional, and all dot-aspects you want to specify)
%% ArcFunction should take two  node id's as input and should return an list of arcRecords
%%       arc(color: DotColorVS % optional,
%%           style: DotArcStyleVS ... % all optional, and all dot-properties you want to specify, or none)
%%      e.g.  to use invisible arcs, set Arc.style=invis
%%
%% {GW rebuild()} %% to re-build the nodes and arcs, usefull for building consecutive versions of graphs
%% {GW rebuildArcs()}  %%to re-build arcs only.
%% {GW writeToNewFileNamed(FileName)}  % opens, over-writes and closes the file
%% {GW writeJpg(JpgFileName)}  % opens, over-writes and closes the file
%%%%%%%%%%%%%%%%%%%


functor
import Open OS  Inspector
export DotGraphWrapper
define
   class DotGraphWrapper
      attr f fileName nodelist edgeLabels colors getArcs getNode nodes arcs complete % nodes and arcs are dictionaries
      meth init(nodes:Ns edgeLabels:Lbls colors:Clrs getNode:Fnode getArcs:Farcs)
	 nodelist := Ns
	 getNode := Fnode
	 getArcs := Farcs
	 complete := false
	 edgeLabels := Lbls
	 colors := Clrs
	 {self rebuild()}
      end
      
      %% private writing to the file
      meth OpenFile()
	 f := {New Open.file
	       init(name: @fileName
		    flags: [write create truncate])}
      end
      meth CloseFile()
	 {@f close()}
		 %{Inspector.inspect closedFile}
      end
      meth WriteIntro
	 {@f write(vs:"digraph G{ \n")}
		 %{Inspector.inspect wroteIntro}
      end
      meth WriteLegend
	 Len = {Length @edgeLabels}
      in
	 {@f write(vs:"subgraph cluster0 { \nnode[color=white] \nedge[style=invis]\n")}
	 for I in 1 .. Len Lbl in @edgeLabels Col in @colors do
	    {@f write(vs:"legend"#I#" [label=\""#Lbl#"\" fontcolor=\""#Col#"\"]\n")}
	    if I < Len then   {@f write(vs:"legend"#I#"->legend"#I+1#"\n")}
	    end
	 end
	 {@f write(vs:"}\n")}
      end
      meth WriteEnd
	 {@f write(vs: "}\n")}
		 %{Inspector.inspect wroteEnd}
      end
      meth WriteNodes  %Make sure build() is called first!
	 {ForAll {Dictionary.entries @nodes}
	  proc{$ Id#Node}
	     Params = for Feat#Fld in {Record.toListInd Node}
			 append: App
		      do {App {VirtualString.toString Feat#"=\""#Fld#"\" "}}
		      end
	  in
	     {@f write(vs: Id#" ["#Params#"]\n")}
	  end}
      end
      meth WriteArcs() 
	 {ForAll {Dictionary.entries @arcs}
	  proc{$ N1#Dict2}
	     {ForAll {Dictionary.entries Dict2}
	      proc{$ N2#Arcs}
		 for Arc in Arcs do
		    Params = for Feat#Fld in {Record.toListInd Arc}
				append: App
			     do {App {VirtualString.toString Feat#"=\""#Fld#"\" "}}
			     end
		 in
		    {@f write(vs: N1#"->"#N2#" ["#Params#"]\n")}
		 end
	      end}
	  end}
      end
      meth WriteGraph()
	 if @complete then 
		 %{Inspector.inspect willWriteGraphNow}
	    {self OpenFile}
		 %{Inspector.inspect fileIsOpen}
	    try {ForAll [WriteIntro WriteNodes WriteArcs() WriteLegend WriteEnd CloseFile] self}
	    catch _ then {self CloseFile} % {Inspector.inspect E}
	    end
	 else raise 'WriteGraph() was called before graph was complete' end
	 end
      end
      
	  %private building the dictionaries
      
      meth ReadArcs(FromId ToId)
	 try 
	    Arcs = {@getArcs FromId ToId}
	 in
	    if Arcs \= nil then
	       if {Not {Dictionary.member @arcs FromId}}
	       then @arcs.FromId:={NewDictionary}
	       end
	       @arcs.FromId.ToId := Arcs
	    end
	 catch _ then {Inspector.inspect self}
	 end
      end
	 
      
      meth ReadNode(Id)
	 @nodes.Id := {@getNode Id}
      end

      %public methods
      meth rebuildArcs()
	 arcs:={NewDictionary}	 
	 for N1 in @nodelist do
	    for N2 in @nodelist do
	       {self ReadArcs(N1 N2)}
	    end
	 end
      end
      meth rebuild()
	 complete:=false
	 nodes:={NewDictionary}
	 {ForAll @nodelist proc{$ Id} {self ReadNode(Id)} end}
	 {self rebuildArcs}
	 complete:=true
      end
      meth writeDot(FileName)
	 fileName := FileName
	 {self WriteGraph()}
      end
      meth getMainFileNamePart(FileName Reply)
	 Tkns = {String.tokens {VirtualString.toString FileName} &.}
	 Len = {List.length FileName}
      in
	 if {Length Tkns} >= 2 then
	    Appx = {List.last Tkns}
	 in
	    case Appx
	    of "jpg" then  Reply = {List.takeWhileInd FileName fun{$ I _} I < Len - 3 end}
	   % [] "svg" then  Reply = {List.takeWhileInd FileName fun{$ I _} I < Len -3 end}
	    [] "dot" then  Reply = {List.takeWhileInd FileName fun{$ I _} I < Len -3 end}
	    else Reply = FileName
	    end
	 else Reply = FileName
	 end
      end
      meth writeJpg(FileName)
	 MainPart = {self getMainFileNamePart(FileName $)}
	 DotName = {Append MainPart ".dot"}
	 JpgName = {Append MainPart ".jpg"}
	 % SVGName = {Append MainPart ".svg"}
      in
	 fileName := DotName
	 {self WriteGraph()}
	 {OS.system "dot -Tjpg "#DotName#" -o "#JpgName _}
	 % {OS.system "dot -Tsvg "#DotName#" -o "#SVGName _}
	 % {OS.system "convert "#SVGName#" "#JpgName _}
      end
   end
end   

