#! /usr/bin/python

import sys,time,re
import Levenshtein
from math import log10 as log
from math import factorial as fact


###################################################################################
# CLASS Node
# Represents a node in the hypergraph
###################################################################################
class Node:
    #---------------------------------------------------
    def __init__(self, idx, out, rhs, sons, edge_lsc, inside_lsc):
        self.__idx__ = idx
        self.__parents__ = []
        self.__sons__ = [(tuple(rhs),tuple(sons),edge_lsc)]
        self.__out__ = out.strip()
        self.__inside_lsc__ = inside_lsc
        self.__outside_lsc__ = 0.0
        self.__outside_parent__ = None
    #---------------------------------------------------
     
    #---------------------------------------------------
    # converts node to string
    def __str__(self):
        output = "H: "+str(self.__idx__)+" => \n"
        indent = ' '*len(output)
        output += indent+"out    : \""+str(self.__out__)+"\"\n"
        output += indent+"inside : "+str(self.__inside_lsc__)+"\n"
        output += indent+"outside: "+str(self.__outside_lsc__)+" -> "+str(self.__outside_parent__)+"\n"
        output += indent+"parents: "+str(self.__parents__)+"\n"
        output += indent+"sons   : \n"
        s_indent = indent+' '*len("sons   : ")
        for t in self.__sons__:
            output += s_indent+"<< "+str(t)+" >>\n"
        return output
    #---------------------------------------------------

    #---------------------------------------------------
    # returns True if node has no parents
    def isHead(self):
        return len(self.__parents__)==0
    #---------------------------------------------------

    #---------------------------------------------------
    # add a new parent to the node
    def addParent(self, parent, edge_lsc):
        self.__parents__.append((parent,edge_lsc))
    #---------------------------------------------------

    #---------------------------------------------------
    # adds a new son, for recombined hypotheses
    def addSon(self, rhs, sons, edge_lsc):
        self.__sons__.append( (tuple(rhs),tuple(sons),edge_lsc) )
    #---------------------------------------------------    

    #---------------------------------------------------
    # sets the index of the output string
    def setOutside(self, outside_parent, outside_lsc):
        self.__outside_lsc__ = outside_lsc
        self.__outside_parent__ = outside_parent
    #---------------------------------------------------

    #---------------------------------------------------
    # sets the string covered by the node
    def setCoveredString(self, out):
        self.__out__ = out.strip()
    #---------------------------------------------------
    
    #---------------------------------------------------
    # returns the string covered by the node
    def getCoveredString(self):
        return self.__out__.strip()
    #---------------------------------------------------

    #---------------------------------------------------
    # returns node idx
    def getIdx(self):
        return self.__idx__
    #---------------------------------------------------    

    #---------------------------------------------------
    # return list of son tuples
    def getSons(self):
        return self.__sons__[:]
    #---------------------------------------------------
    
    #---------------------------------------------------
    # return list of parent indexes
    def getParents(self):
        return self.__parents__[:]
    #---------------------------------------------------

    #---------------------------------------------------
    # returns best parent edge
    def getOutsideParent(self):
        return self.__outside_parent__
    #---------------------------------------------------

    #---------------------------------------------------
    # return inside log score
    def getInsideLogScore(self):
        return self.__inside_lsc__
    #---------------------------------------------------    
    
    #---------------------------------------------------
    # return outside log score
    def getOutsideLogScore(self):
        return self.__outside_lsc__
    #---------------------------------------------------    
###################################################################################
# END Hypothesis
###################################################################################





###################################################################################
# CLASS Hypergraph
# Represents a hypergraph and provides functions to operate with it
###################################################################################
class Hypergraph:
    #---------------------------------------------------
    def __init__(self):
        self.__patt__="^\d+[ ]+([\d>\-]+)[ ]+[SX][ ]+\->(.+)[ ]+:[\d \-]*:[ ]+c=([e\.\d\-]+)[ ]+core=\([e\.,\d\-]+\)[ ]+\[\d+\.\.\d+\][ ]*([ \d]+)[ ]*\[total=([e\.\d\-]+)\].*$"
        self.__max_backtrack_iters__ = 2

        self.__regexp__ = re.compile(self.__patt__)
        self.__nodes__ = {}
        self.__num_edges__ = 0
        self.__no_terminal__ = 'X'
        self.__init_node__ = None
        
        self.err_w = 1.0 # default values for error correcting
        self.err_p = 0.1
    #---------------------------------------------------    
        
    #---------------------------------------------------
    # parses a line by regexp
    def __parseLine__(self, line):
        match = self.__regexp__.match(line)
        
        try:
            data_l = match.groups()
            assert len(data_l)==5
        except AttributeError:
            print line.strip()
            sys.exit()
        
        aux = data_l[0].strip().split("->")
        assert len(aux)==1 or len(aux)==2
        idx = int(aux[0])
        rec = None
        if len(aux)==2:
            rec = int(aux[1])
        
        aux = data_l[1].strip().split() 
        rhs = []
        count = 0
        for w in aux:
            if w=='S' or w=='X':
                rhs.append(self.__no_terminal__)
                count += 1
            else:
                rhs.append(w)

        sons = [int(w) for w in data_l[3].strip().split()]
        try:
            assert len(sons)==count
        except AssertionError:
            sys.stderr.write("\nWARNING: shitty line: "+line.strip()+"\n#")
            sons = []
            rhs = [w for w in rhs if w!=self.__no_terminal__]

        c_lsc = float(data_l[2])
        inside_lsc = float(data_l[4])
        return idx, rec, rhs, c_lsc, sons, inside_lsc
    #---------------------------------------------------

    #---------------------------------------------------
    # returns the string corresponding to a given rhs
    def __stringFromRhs__(self, rhs, sons):
        covered_string = ""
        s_pos = 0
        for w in rhs:
            if w != self.__no_terminal__:
                covered_string += w+" "
            else:
                covered_string += self.__nodes__[sons[s_pos]].getCoveredString()+" "
                s_pos += 1
        return covered_string
    #---------------------------------------------------

    #---------------------------------------------------
    # adds new hypothesis to hypergraph
    def addNewHypothesis(self, line):
        # add new node or update recombined node
        self.__num_edges__ += 1
        try:
            (idx,rec,rhs,c_lsc,sons,inside_lsc) = self.__parseLine__(line)
        except TypeError:
            return False

        edge_lsc = inside_lsc - ( sum( [ self.__nodes__[s_idx].getInsideLogScore() for s_idx in sons ] ) )

        if len(rhs)==1 and rhs[0]=="<s>":
            self.__init_node__ = idx

        if rec == None:
            covered_string = self.__stringFromRhs__(rhs,sons)
            new_node = Node(idx, covered_string, rhs, sons, edge_lsc, inside_lsc)
            self.__nodes__[idx] = new_node
            n_idx = idx
        else:
            self.__nodes__[rec].addSon(rhs, sons, edge_lsc)
            n_idx = rec
        for s_idx in sons:
            self.__nodes__[s_idx].addParent(n_idx,edge_lsc)
    #---------------------------------------------------    

    #---------------------------------------------------
    # Outside: update outside_lsc and outside parent 
    def __outside__(self):  
        ordered_keys = sorted(self.__nodes__, reverse=True)
        for n_idx in ordered_keys:
            node=self.__nodes__[n_idx]
            max_outside_lsc = float("-inf")
            max_outside_parent = None
            if node.isHead():
                node.setOutside(None,0.0)
            else:
                for p_idx,p_edge_lsc in node.getParents():
                    outside_lsc = self.__nodes__[p_idx].getOutsideLogScore()+p_edge_lsc
                    if outside_lsc>max_outside_lsc:
                        max_outside_lsc = outside_lsc
                        max_outside_parent = p_idx
                node.setOutside(max_outside_parent,max_outside_lsc)
    #---------------------------------------------------

    #---------------------------------------------------
    # configure hypergraph for future ITP requests
    def configure(self, err_w, err_p):
        self.err_w = err_w
        self.err_p = err_p
        self.__outside__()
    #---------------------------------------------------

    #---------------------------------------------------
    # return the best matching node among valid nodes
    def __searchNbestNodeMatchRestricted__(self, segm_s, segm_best, valid_nodes, is_prefix):
        # TODO:
        segm = " ".join(segm_s).strip()
        n = len(segm)
        # max_lsc = float("-inf")
        # max_node = None
        
        nbest_nodes = []
        for n_idx in valid_nodes:
            covered_sent = self.__nodes__[n_idx].getCoveredString().strip()
            if not is_prefix or (is_prefix and covered_sent[0:3] == "<s>"): 
                covered_sent = covered_sent.replace("|UNK|UNK|UNK","").replace("<s>","").replace("</s>","").strip()
                d = Levenshtein.distance(segm,covered_sent)
                d = min(d,n)
                err_lsc = d*log(self.err_p) + (n-d)*log(1.0-self.err_p) + log(fact(n))-(log(fact(d))+log(fact(n-d)))
                itp_lsc = self.__nodes__[n_idx].getInsideLogScore()+self.__nodes__[n_idx].getOutsideLogScore()
                cur_lsc = itp_lsc+self.err_w*err_lsc #inside x outside x err**err_w
                # if cur_lsc > max_lsc:
                #     max_lsc = cur_lsc
                #     max_itp_lsc = itp_lsc
                #     max_node = n_idx
                if len(nbest_nodes)<=segm_best or cur_lsc>nbest_nodes[0][0]:
                    nbest_nodes.append((cur_lsc,itp_lsc,n_idx))
                    nbest_nodes = sorted(nbest_nodes)[-segm_best:]
                    #print nbest_nodes
        #return max_lsc,max_itp_lsc,max_node
        still_more_options = True
        if len(nbest_nodes)<segm_best:
            still_more_options = False
        return nbest_nodes[0],still_more_options
    #---------------------------------------------------

    #---------------------------------------------------
    # compute siblings of a given node
    def __family__(self, n_idx):
        ancestors = {} # compute parents
        to_process = dict([(p_tuple[0],True) for p_tuple in self.__nodes__[n_idx].getParents()])
        first_sons = {}
        while len(to_process)>0: # compute ancestors
            c_idx,_ = to_process.popitem()
            for p_idx,_ in self.__nodes__[c_idx].getParents():
                if p_idx not in to_process and p_idx not in ancestors:
                    to_process[p_idx]=True
            ancestors[c_idx]=True
        
        # compute first sons, share edge with ancestor, but not ancestor themselves
        for c_idx in ancestors:
            for _,sons,_ in self.__nodes__[c_idx].getSons():
                if len(sons)==2:
                    if sons[0] in ancestors or sons[0]==n_idx:
                        if sons[1] not in ancestors and sons[1] not in first_sons and sons[1]!=n_idx:
                            first_sons[sons[1]]=True
                    # elif sons[1] in ancestors or sons[1]==n_idx:
                    #     if sons[0] not in ancestors and sons[0] not in first_sons and sons[0]!=n_idx:
                    #         first_sons[sons[0]]=True
        siblings = {} # compute rest of siblings
        to_process = first_sons
        while len(to_process)>0:
            c_idx,_ = to_process.popitem()
            for _,sons,_ in self.__nodes__[c_idx].getSons():
                for s_idx in sons:
                    if s_idx not in to_process and s_idx not in siblings and s_idx not in ancestors and s_idx!=n_idx:
                        to_process[s_idx]=True
            siblings[c_idx]=True
        return ancestors,siblings
    #---------------------------------------------------    

    #---------------------------------------------------
    # return a list with the best matching nodes
    def __searchBestNodesMatch__(self, isles_s):
        sys.stderr.write("# Searching for best derivation ... ")
        init_time = time.time()
        if len(isles_s)==0:
            #node=self.__nodes__[self.__init_node__]
            #ec_lsc = node.getInsideLogScore()+node.getOutsideLogScore()
            #return [([],self.__init_node__,ec_lsc,ec_lsc)]
            isles_s = ['<s>']
        
        # backtracking to obtain best set of nodes
        valid_nodes = [ n_idx for n_idx in sorted(self.__nodes__) if len(self.__nodes__[n_idx].getParents())>0 ]
        nodes_list = []
        first_segm = True
        segm_list = [ segm.strip().split() for segm in " ".join(isles_s).strip().split("<+>") if len(segm.strip())>0 ]
        stack=[]
        segm_idx = 0
        segm_best = 1
        while segm_idx < len(segm_list):
            segm_s = segm_list[segm_idx]
            (ec_lsc,itp_lsc,base_node),still_more_nodes = self.__searchNbestNodeMatchRestricted__(segm_s, segm_best, valid_nodes, first_segm)
            bn_ancestors,bn_siblings = self.__family__(base_node)
            bn_valid_nodes = [n_idx for n_idx in bn_siblings if n_idx in valid_nodes]
            #print base_node,len(bn_valid_nodes),(len(segm_list)-segm_idx-1),still_more_nodes
            while len(bn_valid_nodes) < (len(segm_list)-segm_idx-1) and len(valid_nodes)>segm_best and still_more_nodes and segm_best<self.__max_backtrack_iters__: 
                # dejamos al menos tantos nodos como segmentos quedan
                segm_best+=1
                (ec_lsc,itp_lsc,base_node),still_more_nodes = self.__searchNbestNodeMatchRestricted__(segm_s, segm_best, valid_nodes, first_segm)
                bn_ancestors,bn_siblings = self.__family__(base_node)
                bn_valid_nodes = [n_idx for n_idx in bn_siblings if n_idx in valid_nodes]
                #print "->",segm_best,base_node,len(bn_valid_nodes),(len(segm_list)-segm_idx-1),still_more_nodes
            #print segm_best,self.__max_backtrack_iters__
            if len(bn_valid_nodes) < (len(segm_list)-segm_idx-1) or not still_more_nodes or segm_best>=self.__max_backtrack_iters__: # backtracking
                try:
                    segm_idx,valid_nodes,segm_best,first_segm=stack.pop()
                    nodes_list.pop()
                    segm_best+=1
                except IndexError:
                    self.__max_backtrack_iters__ += 1
                    first_segm = True
                    sys.stderr.write("#")
                sys.stderr.write(str(segm_idx))
                #print "bt:",segm_idx,segm_list[segm_idx],segm_best,len(valid_nodes)
                #print nodes_list
            else:
                stack.append((segm_idx,valid_nodes,segm_best,first_segm))
                nodes_list.append((segm_s,base_node,ec_lsc,itp_lsc,bn_ancestors))
                valid_nodes = bn_valid_nodes
                #print len(valid_nodes),base_node,segm_best,segm_s
                first_segm = False
                segm_idx += 1
                segm_best = 1

            if segm_idx == len(segm_list):
                #TODO: include consensus derivation in backtracking
                common_derivation,consensus,ancestors_coverage = self.__consensusDerivation__(nodes_list)
                if common_derivation:
                    self.__max_backtrack_iters__ = 2
                    timestamp = time.time()-init_time
                    sys.stderr.write(" Done ( "+str(timestamp)+" s.)\n")
                    return nodes_list,consensus,ancestors_coverage
                else:
                    # backtracking because no common derivation
                    try:
                        segm_idx,valid_nodes,segm_best,first_segm=stack.pop()
                        nodes_list.pop()
                        segm_best+=1
                    except IndexError:
                        self.__max_backtrack_iters__ += 1
                        first_segm = True
    #---------------------------------------------------

    #---------------------------------------------------
    # Return a derivation common to all nodes
    def __consensusDerivation__(self, nodes):
        heads = dict( [(n_idx,True) for n_idx in self.__nodes__] )
        ancestors_cover = {}
        base_leaves = []
        #TODO: contar cover solo si suben por el mismo edge
        for node_pos,node_tuple in enumerate(nodes):
            _,base_node,_,_,ancestors=node_tuple
            if base_node not in ancestors_cover:
                base_leaves.append(base_node)
                ancestors_cover[base_node] = []
            ancestors_cover[base_node].append(node_pos)
            n_heads = {}
            for n_idx in ancestors:
                if n_idx not in ancestors_cover:
                    ancestors_cover[n_idx] = []
                ancestors_cover[n_idx].append(node_pos)
                if len(self.__nodes__[n_idx].getParents())==0:
                    n_heads[n_idx]=True
            heads = dict([(n_idx,True) for n_idx in n_heads if n_idx in heads])
        try:
            assert len(heads)>0
        except AssertionError:
            print nodes
            print heads
            #return False,[],ancestors_cover
            sys.exit()

        # eliminar invalid covers
        #print len(ancestors_cover)
        valid_covers = dict([(tuple(range(i,j)),True) for i in range(len(nodes)+1) for j in range(i+1,len(nodes)+1)]) # only ordered covers
        ancestors_keys = ancestors_cover.keys()
        for n_idx in ancestors_keys:
            if tuple(ancestors_cover[n_idx]) not in valid_covers:
                ancestors_cover.pop(n_idx)
        #print len(ancestors_cover)
        # print heads

        raw_consensus = []
        dead_ends = {}
        node_dependency = {}
        to_process = dict([ (n_idx,range(len(nodes))) for n_idx in heads ])
        next_to_process = {}
        while len(to_process)>0:
            #print to_process
            for n_idx,coverage in to_process.items():
                #print n_idx,coverage
                coverage.sort()
                node_dependency[n_idx]=[]
                valid_uphill_edge = False
                for _,sons,_ in self.__nodes__[n_idx].getSons():
                    n_cover = []
                    for s_idx in sons:
                        if s_idx in ancestors_cover:
                            n_cover.append(ancestors_cover[s_idx])
                        else:
                            n_cover.append([])
                    #print "->",sons,n_cover
                    if sorted(sum(n_cover,[]))==coverage:
                        valid_uphill_edge = True
                        node_dependency[n_idx].append((sons,n_cover))
                        #print n_idx,coverage,"->",sons,n_cover
                        for s_pos in range(len(sons)):
                            if n_cover[s_pos]!=[] and sons[s_pos]!=n_idx:
                                if sons[s_pos] not in next_to_process and sons[s_pos] not in to_process and sons[s_pos] not in raw_consensus:
                                    next_to_process[sons[s_pos]] = n_cover[s_pos]
                if valid_uphill_edge:
                    raw_consensus.append(n_idx)
                else:
                    dead_ends[n_idx]=True
            to_process = next_to_process
            next_to_process = {}        

        seen = {}
        for _,base_node,_,_,_ in nodes:
            seen[base_node]=True
        consensus = []
        for n_idx in reversed(raw_consensus):
            if n_idx not in seen:
                consensus.append(n_idx)
                seen[n_idx] = True
        consensus.sort()

        #flag detectando si al menos hay una derivacion comun
        #print dead_ends
        clean_consensus=[]
        for n_idx in consensus:
            dependencies = node_dependency[n_idx]
            #print n_idx,dependencies
            alive=False
            for sons,n_cover in dependencies: 
                # hijos con coverage no en dead_ends
                edge_alive = True
                being_inspected = [sons[s_pos] for s_pos in range(len(sons)) if n_cover[s_pos]!=[]]
                for s_idx in being_inspected:
                    if s_idx in dead_ends and s_idx not in base_leaves:
                        edge_alive=False
                        break
                if edge_alive:
                    alive = True
                    break
            #print alive
            if alive:
                clean_consensus.append(n_idx)
            else:
                dead_ends[n_idx]=True
        #print len(consensus),len(clean_consensus)

        # TODO: ademas derivacion para cada base_leave, no solo para una
        #common_derivation = (len(clean_consensus)!=0)
        common_derivation = False
        for n_idx in heads:
            common_derivation = common_derivation or (n_idx in clean_consensus)

        return common_derivation,consensus,ancestors_cover
    #---------------------------------------------------    


    #---------------------------------------------------
    # return translation resulting from uphill
    # derivation between prev_idx and next
    # prev_idx covers covered_string
    def __uphill_derivation__(self,next_idx,mod_covered_strings):
        max_edge = (None, None, float("-inf"))
        max_step_lsc = float("-inf")
        max_coverage = []
        next = self.__nodes__[next_idx]
        for son_tuple in next.getSons(): # search for best edge
            _,sons,edge_lsc = son_tuple
            for s_idx in sons:
                if s_idx in mod_covered_strings:
                    step_lsc = sum([self.__nodes__[s_idx].getInsideLogScore() for s_idx in sons])+edge_lsc
                    step_cover = list(set( sum([mod_covered_strings[s_idx][1] for s_idx in sons if s_idx in mod_covered_strings],[])))
                    if len(step_cover)>len(max_coverage):
                        max_edge = son_tuple
                        max_step_lsc = step_lsc
                        max_coverage = step_cover
                        #print "S1:",next_idx,sons,step_lsc,step_cover
                    elif len(step_cover)==len(max_coverage) and step_lsc>max_step_lsc:
                        max_edge = son_tuple
                        max_step_lsc = step_lsc
                        max_coverage = step_cover
                        #print "S2:",next_idx,sons,step_lsc,step_cover
                    break
        rhs,sons,edge_lsc = max_edge
        if not rhs: # some nodes in consensus are not valid
            return None,None,None
        next_covered_string = ""
        pos = 0
        for w in rhs:
            if w==self.__no_terminal__:
                if sons[pos] in mod_covered_strings:
                    next_covered_string += mod_covered_strings[sons[pos]][0]+" "
                else:
                    next_covered_string += self.__nodes__[sons[pos]].getCoveredString()+" "
                pos += 1
            else:
                next_covered_string += w+" "
        return next_covered_string,max_step_lsc,max_coverage
    #---------------------------------------------------            

    #---------------------------------------------------
    # return best translation that completes user isles        
    def getTranslation(self, isles_s):
        # TODO: search for best nodes and obtain consensus derivation
        nodes_list,consensus,ancestors_coverage = self.__searchBestNodesMatch__(isles_s)
        #print nodes_list
        #print consensus

        mod_covered_strings = {}
        for segm_pos,segm_tuple in enumerate(nodes_list):
            segm_s,base_node,_,_,_ = segm_tuple
            mod_covered_strings[base_node]=(" ".join(segm_s),[segm_pos])

        #print mod_covered_strings
        for next_idx in consensus:
            next_covered_string,step_lsc,next_cover = self.__uphill_derivation__(next_idx,mod_covered_strings)
            if next_covered_string and sorted(next_cover)==ancestors_coverage[next_idx]: # some nodes in consensus are not valid
                mod_covered_strings[next_idx] =(next_covered_string,next_cover)
            #     print "C:",next_idx,next_cover,next_covered_string
            # else:
            #     print "Cover:",next_idx,next_cover,"-",ancestors_coverage[next_idx]
        assert len(next_cover)==len(nodes_list)
        # try:
        #     assert len(next_cover)==len(nodes_list)
        # except AssertionError:
        #     sys.stderr.write("WARNING: potentially incomplete coverage.\n")
        return step_lsc,step_lsc,next_covered_string
    #---------------------------------------------------

    #---------------------------------------------------
    # return number of nodes 
    def numberOfNodes(self):       
        return len(self.__nodes__)
    #---------------------------------------------------

    #---------------------------------------------------
    # return number of nodes 
    def numberOfEdges(self):       
        return self.__num_edges__
    #---------------------------------------------------
###############################################################################
# END: Hypergraph    
###############################################################################    

            













###############################################################################
# CLASS HypergraphReader
# Provides a wrapper to read several hypergraphs from a single file
# hypergraphs are indexed by hypothesis number
###############################################################################
class HypergraphReader:
    #--------------------------------------------------------
    def __init__(self,file_name):
        self._file_name = file_name
        self._file_descriptor = open(self._file_name,'r')
        self._buffer = self._file_descriptor.readline()
    #--------------------------------------------------------
    
    #--------------------------------------------------------    
    # Reads next hypergraph from file
    def nextHypergraph(self):
        hg = Hypergraph()
        hyp_line = self._buffer
        num_hyp = int(hyp_line.strip().split()[0])
        num_hyp_ant = num_hyp
        
        while hyp_line != "" and num_hyp_ant == num_hyp:
            hg.addNewHypothesis(hyp_line)

            num_hyp_ant = num_hyp
            hyp_line = self._file_descriptor.readline()
            try:
                num_hyp = int(hyp_line.strip().split()[0])
            except IndexError:
                pass
        self._buffer = hyp_line
        return hg
    #--------------------------------------------------------

    #--------------------------------------------------------
    # End of file flag, true if more hypergraphs to be read
    def eof(self):
        if len(self._buffer) == 0:
            return True
        else:
            return False
    #--------------------------------------------------------
###############################################################################
# END: HypergraphReader    
###############################################################################




###############################################################
###############################################################
##  Auxiliary function to compute user feedback
###############################################################
def lev_path(s1, s2):
    previous_row = xrange(len(s2) + 1)
    previous_ed = ['']*(len(s2) + 1)
    for i, c1 in enumerate(s1):
        current_row = [i+1]
        current_ed = ['I'*(i+1)]
        for j, c2 in enumerate(s2):
            # insertions = (previous_row[j+1] + len(c1), previous_ed[j+1]+'I') 
            # deletions = (current_row[j] + len(c2), current_ed[j]+'D')       
            # substitutions = (previous_row[j] + Levenshtein.distance(c1,c2), previous_ed[j]+'S')
            insertions = (previous_row[j+1] + 1, previous_ed[j+1]+'I') 
            deletions = (current_row[j] + 1, current_ed[j]+'D')       
            substitutions = (previous_row[j] + (c1!=c2), previous_ed[j]+'S')
            edit_op = min(substitutions, insertions, deletions)
            current_row.append(edit_op[0])
            current_ed.append(edit_op[1])

        previous_row = current_row
        previous_ed = current_ed
    return previous_row[-1],previous_ed[-1]
###############################################################

###############################################################
##  Function that computes user feedback
###############################################################
def user(tra_s, ref_s):
    ed_cost,ed_path = lev_path(tra_s,ref_s)
    assert len(ed_path.replace('D',''))==len(tra_s) # do not take into account deleted reference words

    #print ref_s
    #print tra_s
    #print ed_cost,ed_path
    isles = []
    user_feedback = []
    ref_pos = tra_pos = mouse_actions = strokes = 0
    add_feedback = end_interaction = True
    user_stroke_pos = None
    for ed_op in ed_path:
        #print ed_op,ref_pos,ref_s[ref_pos],tra_pos,tra_s[tra_pos]
        if ed_op == "S":
            if ref_s[ref_pos]==tra_s[tra_pos]:
                isles.append(ref_s[ref_pos])
                mouse_actions+=1
                user_feedback.append("M")
            elif add_feedback:
                isles.append(ref_s[ref_pos])
                add_feedback = False
                strokes += 1
                user_stroke_pos = len(isles)-1
                user_feedback.append("W")
            else:
                user_feedback.append('E')
                end_interaction = False
                if len(isles)==0 or isles[-1]!="<+>":
                    isles.append('<+>')
            ref_pos += 1
            tra_pos += 1
        elif ed_op == 'I':
            user_feedback.append('E')
            tra_pos += 1
        else: # Deleted reference word TODO, what if deleted is equal?
            if add_feedback:
                isles.append(ref_s[ref_pos])
                if ref_pos<len(ref_s) and tra_pos<len(tra_s) and ref_s[ref_pos]==tra_s[tra_pos]:
                    mouse_actions += 1
                else:
                    add_feedback = False
                    strokes += 1
                    user_stroke_pos = len(isles)-1
                    
            else:
                end_interaction = False
                if len(isles)==0 or isles[-1]!="<+>":
                    isles.append('<+>')
            ref_pos += 1
            
    return isles,user_feedback,end_interaction,mouse_actions,strokes,user_stroke_pos
###############################################################    
###############################################################



###############################################################
###############################################################
##   MAIN entry to the program
###############################################################
###############################################################
if len(sys.argv)!=6:
    sys.stderr.write("USAGE: "+sys.argv[0]+" <hipergraphFile> <source> <reference> <err_w> <err_p>\n")
    sys.exit()

file_name_hypergraph = sys.argv[1]
reader = HypergraphReader(file_name_hypergraph)

sys.stderr.write("# Starting hierarquical IMT process.\n")

sys.stderr.write("# Reading source sentences ... ")
aux = time.time()
file_name_sources = sys.argv[2]
f = open(file_name_sources,'r')
sources = [l.strip().split() for l in f]
f.close()
sys.stderr.write("Done ( "+str(time.time()-aux)+" s. )\n")

sys.stderr.write("# Reading reference translations ... ")
aux = time.time()
file_name_references = sys.argv[3]
f = open(file_name_references,'r')
references = [l.strip().split() for l in f]
f.close()
sys.stderr.write("Done ( "+str(time.time()-aux)+" s. )\n")

assert len(sources)==len(references)

err_w = float(sys.argv[4])
err_p = float(sys.argv[5])
if err_p<=0:
    sys.stderr.write("# Error probability rounded to 0.00001\n")
    err_p = 0.00001
if err_p>=1:
    sys.stderr.write("# Error probability rounded to 0.99999\n")
    err_p = 0.99999

########################################################################
# no need for individua scores, simple formulation
########################################################################
word_strokes = 0
mouse_actions = 0
ref_words = 0
for s_idx in range(len(sources)):
    init_time = time.time()
    src_s = sources[s_idx]
    ref_s = references[s_idx]
    if not reader.eof():
        aux = time.time()
        sys.stderr.write("# Reading next hypergraph...")
        hg = reader.nextHypergraph()
        hg.configure(err_w,err_p)
        sys.stderr.write(" Done ( "+str(time.time()-aux)+" s., "+str(hg.numberOfNodes())+" hyps. "+str(hg.numberOfEdges())+" edg. )\n")
    else:
        sys.stderr.write("ERROR: no more hypergraphs and still translations remaining.\n")
        sys.exit()

    timestamp = time.time()-init_time
    sys.stderr.write("SRC "+str(s_idx)+" ( "+str(timestamp)+" ): "+" ".join(src_s)+"\n")
    sys.stderr.write("REF "+str(s_idx)+" ( "+str(timestamp)+" ): "+" ".join(ref_s)+"\n")

    if s_idx<0:
        continue

    user_isles_s = []
    strokes = 0
    while True:
        ec_lsc,itp_lsc,out = hg.getTranslation(user_isles_s)
        tra_s = out.replace("|UNK|UNK|UNK","").replace("<s>","").replace("</s>","").strip().split()

        user_isles_s,user_feedback,end_interaction,ma,ws,user_stroke_pos = user(tra_s, ref_s)
        strokes += ws

        # output trace
        timestamp = time.time()-init_time
        #sys.stderr.write("Tra ( "+str(timestamp)+" ): "+" ".join([tra_s[pos]+"<"+user_feedback[pos]+">" for pos in range(len(tra_s))])+"\n")
        sys.stderr.write("TRA "+str(s_idx)+" ( "+str(timestamp)+" ): "+" ".join(tra_s)+" ||| "+str(ec_lsc)+" ("+str(itp_lsc)+")\n")
        
        aux_out = user_isles_s[:]
        if user_stroke_pos:
            aux_out[user_stroke_pos] = "["+aux_out[user_stroke_pos]+"]"
        sys.stderr.write("# ISLE: "+" ".join(aux_out)+"\n")
        
        #print "T:",tra_s
        #print "R:",ref_s
        #print " --> I:"," ".join(user_isles_s)
        #print "U:",user_feedback,end_interaction

        if end_interaction:
            mouse_actions += (ma-strokes)
            word_strokes += strokes
            ref_words += len(ref_s)
            wsmr = (word_strokes+mouse_actions)/float(ref_words)
            wsr = word_strokes/float(ref_words)
            sys.stderr.write("#------> cur: "+str((user_feedback.count("S"),strokes,ma)))
            sys.stderr.write(" ws: "+str(word_strokes)+" ma: "+str(mouse_actions)+" rw: "+str(ref_words))
            sys.stderr.write(" -> wsr: "+str(wsr)+" wsmr: "+str(wsmr)+"\n")
            break
    #sys.exit()
            
sys.stdout.write( str(word_strokes/float(ref_words))+"\n" )
