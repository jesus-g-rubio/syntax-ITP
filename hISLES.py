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
    def __searchBestNodeMatchRestricted__(self, segm_s, valid_nodes, is_prefix):
        # TODO:
        segm = " ".join(segm_s).strip()
        n = len(segm)
        max_lsc = float("-inf")
        max_node = None
        
        for n_idx in valid_nodes:
            covered_sent = self.__nodes__[n_idx].getCoveredString().strip()
            if not is_prefix or (is_prefix and covered_sent[0:3] == "<s>"): 
                covered_sent = covered_sent.replace("|UNK|UNK|UNK","").replace("<s>","").replace("</s>","").strip()
                d = Levenshtein.distance(segm,covered_sent)
                d = min(d,n)
                err_lsc = d*log(self.err_p) + (n-d)*log(1.0-self.err_p) + log(fact(n))-(log(fact(d))+log(fact(n-d)))
                itp_lsc = self.__nodes__[n_idx].getInsideLogScore()+self.__nodes__[n_idx].getOutsideLogScore()
                cur_lsc = itp_lsc+self.err_w*err_lsc #inside x outside x err**err_w
                if cur_lsc > max_lsc:
                    max_lsc = cur_lsc
                    max_itp_lsc = itp_lsc
                    max_node = n_idx
        return max_node,max_lsc,max_itp_lsc
    #---------------------------------------------------

    #---------------------------------------------------
    # compute siblings of a given node
    def __family__(self, n_idx):
        ancestors = {} # compute parents
        to_process = dict([(p_tuple[0],True) for p_tuple in self.__nodes__[n_idx].getParents()])
        first_sons = {}
        while len(to_process)>0:
            c_idx,_ = to_process.popitem()
            for p_idx,_ in self.__nodes__[c_idx].getParents():
                if p_idx not in to_process and p_idx not in ancestors:
                    to_process[p_idx]=True
            ancestors[c_idx]=True
            for _,sons,_ in self.__nodes__[c_idx].getSons():
                for s_idx in sons:
                    if s_idx not in first_sons and s_idx!=n_idx:
                        first_sons[s_idx]=True
        siblings = {}
        to_process = dict([(k,True) for k in first_sons])
        while len(to_process)>0:
            c_idx,_ = to_process.popitem()
            for _,sons,_ in self.__nodes__[c_idx].getSons():
                for s_idx in sons:
                    if s_idx not in to_process and s_idx not in siblings and s_idx not in ancestors and s_idx!=n_idx:
                        to_process[s_idx]=True
            siblings[c_idx]=True
        return ancestors.keys(),siblings.keys()
    #---------------------------------------------------    

    #---------------------------------------------------
    # return a list with the best matching nodes
    # and consensus derivation including all them
    def __searchBestNodesMatch__(self, isles_s):
        if len(isles_s)==0:
            #node=self.__nodes__[self.__init_node__]
            #ec_lsc = node.getInsideLogScore()+node.getOutsideLogScore()
            #return [([],self.__init_node__,ec_lsc,ec_lsc)]
            isles_s = ['<s>']
        
        # backtracking to obtain best set of nodes
        valid_nodes = sorted(self.__nodes__)
        nodes_list = []
        first_segm = True
        segm_list = [ segm.strip().split() for segm in " ".join(isles_s).strip().split("<+>") if len(segm.strip())>0 ]
        for segm_s in segm_list:
            base_node,ec_lsc,itp_lsc = self.__searchBestNodeMatchRestricted__(segm_s, valid_nodes, first_segm)
            first_segm = False
            bn_ancestors,bn_siblings = self.__family__(base_node)
            valid_nodes = [n_idx for n_idx in bn_siblings if n_idx in valid_nodes]
            #common_ancestors = [n_idx for n_idx in bn_ancestors if n_idx in common_ancestors]
            # TODO: backtracking if valid_nodes vacio
            # TODO: return consensus derivation from ancestors
            nodes_list.append((segm_s,base_node,ec_lsc,itp_lsc))
        return nodes_list
    #---------------------------------------------------

    #---------------------------------------------------
    # return translation resulting from uphill
    # derivation between prev_idx and next
    # prev_idx covers covered_string
    def __uphill_derivation__(self,next,previous_nodes,mod_covered_strings,segm_idx):
        max_edge = (None, None, float("-inf"))
        max_step_lsc = float("-inf")
        max_coverage = []
        for son_tuple in next.getSons(): # search for best edge
            _,sons,edge_lsc = son_tuple
            for s_idx in sons:
                if s_idx in previous_nodes:
                    step_lsc = sum([self.__nodes__[s_idx].getInsideLogScore() for s_idx in sons])+edge_lsc
                    step_cover = list(set( sum([mod_covered_strings[s_idx][2] for s_idx in sons if s_idx in mod_covered_strings] ,[]) ))
                    if len(step_cover)>len(max_coverage):
                        max_edge = son_tuple
                        max_step_lsc = step_lsc
                        max_coverage = step_cover
                    elif len(step_cover)==len(max_coverage) and step_lsc>max_step_lsc:
                        max_edge = son_tuple
                        max_step_lsc = step_lsc
                        max_coverage = step_cover
                    break
                        
        rhs,sons,edge_lsc = max_edge
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
        nodes_list = self.__searchBestNodesMatch__(isles_s)
        
        sys.exit()


        print "NODES:",nodes_list
        # TODO: uphill derivation from various nodes
        # Individual uphill of each one updating information
        mod_covered_strings = {}
        segm_idx = 0
        for segm_s,base_node,ec_lsc,itp_lsc in nodes_list:
            # TODO: uphill decoding encajar diferentes segmentos
            heads = []
            current_nodes = {base_node:True}
            mod_covered_strings[base_node] = (" ".join(segm_s),0.0,[segm_idx])
            while len(current_nodes)>0:
                heads = current_nodes.keys()
                parents = set([ p_tup[0] for c_idx in current_nodes for p_tup in self.__nodes__[c_idx].getParents() ])
                for p_idx in parents:
                    parent_node = self.__nodes__[p_idx]
                    parent_covered_string,step_lsc,coverage = self.__uphill_derivation__(parent_node,current_nodes,mod_covered_strings,segm_idx)
                    
                    #print coverage
                    if p_idx not in mod_covered_strings:
                        mod_covered_strings[p_idx] = (parent_covered_string.strip(),step_lsc,coverage)
                        print "New:",segm_idx, segm_s, mod_covered_strings[p_idx]
                    else:
                        print "Old:",segm_idx, segm_s, mod_covered_strings[p_idx]
                        if len(coverage)>len(mod_covered_strings[p_idx][2]): 
                            mod_covered_strings[p_idx] = (parent_covered_string.strip(),step_lsc,coverage)
                        elif len(coverage)==len(mod_covered_strings[p_idx][2]) and step_lsc>mod_covered_strings[p_idx][1]:
                            mod_covered_strings[p_idx] = (parent_covered_string.strip(),step_lsc,coverage)
                        print "->",mod_covered_strings[p_idx]

                current_nodes = dict([(p_idx,True) for p_idx in parents])
            print "FINAL:",segm_idx,segm_s,"-",heads,"-->",mod_covered_strings[heads[0]]
            segm_idx += 1
        assert len(mod_covered_strings[heads[0]][2])==len(nodes_list)
        return ec_lsc,itp_lsc,mod_covered_strings[heads[0]][0]
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
            insertions = (previous_row[j+1] + 1, previous_ed[j+1]+'I') 
            deletions = (current_row[j] + 1, current_ed[j]+'D')       
            substitutions = (previous_row[j] + (c1!=c2), previous_ed[j]+'S')
            edit_op = min(insertions, deletions, substitutions)
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

    #print ed_path
    isles = []
    user_feedback = []
    ref_pos = tra_pos = mouse_actions = strokes = 0
    add_feedback = end_interaction = True
    for ed_op in ed_path:
        if ed_op == "S":
            if ref_s[ref_pos]==tra_s[tra_pos]:
                isles.append(ref_s[ref_pos])
                mouse_actions+=1
                user_feedback.append("M")
            elif add_feedback:
                isles.append(ref_s[ref_pos])
                add_feedback = False
                strokes += 1
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
        else: # Deleted reference word
            if add_feedback: 
                isles.append(ref_s[ref_pos])
                add_feedback = False
                strokes += 1
            else:
                end_interaction = False
                if len(isles)==0 or isles[-1]!="<+>":
                    isles.append('<+>')
            ref_pos += 1
            
    return isles,user_feedback,end_interaction,mouse_actions,strokes
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
    sys.stderr.write("Src "+str(s_idx)+" ( "+str(timestamp)+" ): "+" ".join(src_s)+"\n")
    sys.stderr.write("Ref "+str(s_idx)+" ( "+str(timestamp)+" ): "+" ".join(ref_s)+"\n")

    user_isles_s = []
    strokes = 0
    while True:
        ec_lsc,itp_lsc,out = hg.getTranslation(user_isles_s)
        tra_s = out.replace("|UNK|UNK|UNK","").replace("<s>","").replace("</s>","").strip().split()

        user_isles_s,user_feedback,end_interaction,ma,ws = user(tra_s, ref_s)
        strokes += ws

        # output trace
        timestamp = time.time()-init_time
        sys.stderr.write("Tra ( "+str(timestamp)+" ): "+" ".join([tra_s[pos]+"<"+user_feedback[pos]+">" for pos in range(len(tra_s))])+" ||| "+str(ec_lsc)+" ("+str(itp_lsc)+")\n")

        #print "T:",tra_s
        #print "R:",ref_s
        print " --> I:"," ".join(user_isles_s)
        #print "U:",user_feedback,end_interaction

        if end_interaction:
            mouse_actions += ma
            word_strokes += strokes
            ref_words += len(ref_s)
            wsmr = (word_strokes+mouse_actions)/float(ref_words)
            wsr = word_strokes/float(ref_words)
            sys.stderr.write("# cur: "+str((user_feedback.count("S"),strokes,ma)))
            sys.stderr.write(" ws: "+str(word_strokes)+" ma: "+str(mouse_actions)+" rw: "+str(ref_words))
            sys.stderr.write(" -> wsr: "+str(wsr)+" wsmr: "+str(wsmr)+"\n")
            break
    #sys.exit()
            
sys.stdout.write( str(word_strokes/float(ref_words))+"\n" )
