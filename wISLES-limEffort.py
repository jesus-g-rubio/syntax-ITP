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
        self.__max_backtrack_iters__ = 2

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
        # 0 hyp=5451 stack=2 back=66 score=-6.759 transition=-1.853 recombined=5352 forward=12736 fscore=-15.721 covered=4-4 out=information
        ls = line.strip().split()

        # skip wordgraph number
        ls.pop(0) 
        
        # node idx
        f = ls.pop(0)
        assert f[:4]=="hyp="
        idx = int(f.strip().split('=')[1])
        
        # stack idx
        f = ls.pop(0)
        assert f[:6]=="stack="
        stack=int(f.strip().split('=')[1])
        if stack==0: # initial hypothesis
            return idx,None, ['<s>'], 0.0, [], 0.0,None,float("-inf")

        # sons
        f = ls.pop(0)
        assert f[:5]=="back="
        son = int(f.strip().split("=")[1])
        sons = [son]
        

        # inside
        f = ls.pop(0)
        assert f[:6]=="score="
        inside_lsc = float(f.strip().split("=")[1])

        # transition
        f = ls.pop(0)
        assert f[:11]=="transition="
        c_lsc = float(f.strip().split("=")[1])

        # recombined and/or forward
        f = ls.pop(0)
        assert f[:11]=="recombined=" or f[:8]=="forward="
        rec = None
        if f[:11]=="recombined=":
            rec = int(f.strip().split("=")[1])
            f = ls.pop(0)
        assert f[:8]=="forward="    
        forw = int(f.strip().split("=")[1])
        if forw==-1:
            forw = None
        
        # forward score
        f=ls.pop(0)
        assert f[:7]=="fscore="
        f_lsc = float(f.strip().split("=")[1])

        # coverage
        f=ls.pop(0)
        assert f[:8]=="covered="

        # rhs
        f=ls.pop(0)
        rhs = [self.__no_terminal__]
        assert f[:4]=="out="
        rhs.append(f.strip().split("=")[1])
        while len(ls)>0:
            rhs.append(ls.pop(0))
        
        #print line.strip()
        #print [idx, rec, rhs, c_lsc, sons, inside_lsc]

        return idx, rec, rhs, c_lsc, sons, inside_lsc, forw, f_lsc
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
            (idx,rec,rhs,c_lsc,sons,inside_lsc,forward,f_lsc) = self.__parseLine__(line)
        except TypeError:
            return False

        edge_lsc = inside_lsc - ( sum( [ self.__nodes__[s_idx].getInsideLogScore() for s_idx in sons ] ) )
        assert (c_lsc-edge_lsc)**2 < 0.001

        if len(rhs)==1 and rhs[0]=="<s>":
            self.__init_node__ = idx
        else:
            # actualizamos outside de nodo base
            if sons[0]==self.__init_node__ and (edge_lsc+f_lsc)>self.__nodes__[self.__init_node__].getOutsideLogScore():
                self.__nodes__[self.__init_node__].setOutside(idx,edge_lsc+f_lsc)

        if rec == None:
            covered_string = self.__stringFromRhs__(rhs,sons)
            new_node = Node(idx, covered_string, rhs, sons, edge_lsc, inside_lsc)
            new_node.setOutside(forward,f_lsc)
            self.__nodes__[idx] = new_node
            n_idx = idx
        else:
            self.__nodes__[rec].addSon(rhs, sons, edge_lsc)
            n_idx = rec
        for s_idx in sons:
            self.__nodes__[s_idx].addParent(n_idx,edge_lsc)
    #---------------------------------------------------    


    #---------------------------------------------------
    # configure hypergraph for future ITP requests
    def configure(self, err_w, err_p):
        self.err_w = err_w
        self.err_p = err_p
    #---------------------------------------------------

    #---------------------------------------------------
    # return the best matching node among valid nodes
    def __searchNbestNodeMatchRestricted__(self, segm_s, segm_best, valid_nodes, first_isle):
        segm = " ".join(segm_s).strip()
        n = len(segm)
        #print "SN:",segm_s, segm_best, len(valid_nodes), first_isle
        
        nbest_nodes = []
        for n_idx in valid_nodes:
            covered_sent_s,inside_lsc = valid_nodes[n_idx]
            #print n_idx,covered_sent_s,inside_lsc
            # all nodes represent prefixes
            # "|||" symbol represents previous matching
            # search for node whith best EC score on the unmatched suffix
            if first_isle:
                covered_sent = " ".join(covered_sent_s).replace("|UNK|UNK|UNK","").replace("</s>","").strip()
                d = Levenshtein.distance(segm,covered_sent)
                d = min(d,n)
                err_lsc = d*log(self.err_p) + (n-d)*log(1.0-self.err_p) + log(fact(n))-(log(fact(d))+log(fact(n-d)))
                itp_lsc = self.__nodes__[n_idx].getInsideLogScore()+self.__nodes__[n_idx].getOutsideLogScore()
                cur_lsc = itp_lsc+self.err_w*err_lsc #inside x outside x err**err_w
                if len(nbest_nodes)<=segm_best or cur_lsc>nbest_nodes[0][0]:
                    nbest_nodes.append((cur_lsc,itp_lsc,n_idx,segm_s))
                    nbest_nodes = sorted(nbest_nodes)[-segm_best:]
                    #print "P",covered_sent,d,err_lsc,itp_lsc,cur_lsc
                    #print "P",nbest_nodes
            else:
                max_suffix_size = len(covered_sent_s)-covered_sent_s.index("|||")-1
                for suffix_size in range(1,max_suffix_size):
                    covered_sent = " ".join(covered_sent_s[-suffix_size:]).replace("|UNK|UNK|UNK","").replace("</s>","").strip()
                    d = Levenshtein.distance(segm,covered_sent)
                    d = min(d,n)
                    err_lsc = d*log(self.err_p) + (n-d)*log(1.0-self.err_p) + log(fact(n))-(log(fact(d))+log(fact(n-d)))
                    itp_lsc = self.__nodes__[n_idx].getInsideLogScore()+self.__nodes__[n_idx].getOutsideLogScore()
                    cur_lsc = itp_lsc+self.err_w*err_lsc #inside x outside x err**err_w
                    if len(nbest_nodes)<=segm_best or cur_lsc>nbest_nodes[0][0]:
                        out_str = covered_sent_s[:-suffix_size]+tuple(segm_s)
                        nbest_nodes.append((cur_lsc,itp_lsc,n_idx,out_str))
                        nbest_nodes = sorted(nbest_nodes)[-segm_best:]
                        #print "I",covered_sent,d,err_lsc,itp_lsc,cur_lsc
                        #print "I", nbest_nodes
        #print nbest_nodes
        #return max_lsc,max_itp_lsc,max_node
        #sys.exit()
        still_more_options = True
        if len(nbest_nodes)<segm_best:
            still_more_options = False
        return nbest_nodes[0],still_more_options
    #---------------------------------------------------


    #---------------------------------------------------
    # compute ancestors of a given node
    def __ancestors__(self,n_idx,n_str,segm_s):
        ancestors = {} # compute parents
        to_process = dict([(p_tuple[0],True) for p_tuple in self.__nodes__[n_idx].getParents()])
        while len(to_process)>0:
            c_idx = min(to_process.keys())
            for p_idx,_ in self.__nodes__[c_idx].getParents():
                if p_idx not in to_process and p_idx not in ancestors:
                    to_process[p_idx]=True
            ancestors[c_idx]=True
            del to_process[c_idx]

        # compute best inside string
        anc_info={}
        anc_info[n_idx]=(tuple(list(n_str)+["|||"]),self.__nodes__[n_idx].getInsideLogScore())
        ancestor_idxs=sorted(ancestors.keys())
        #print n_idx,n_str,segm_s
        #print len(ancestor_idxs)
        #print ancestor_idxs
        while len(ancestor_idxs)>0:
            c_idx = ancestor_idxs.pop(0)
            #print c_idx
            max_lsc = float("-inf")
            early_stop=False
            for rhs,sons,edge_lsc in self.__nodes__[c_idx].getSons():
                if len(sons)==1 and (sons[0] in ancestors or sons[0]==n_idx):
                    #print rhs,sons,edge_lsc
                    s_idx = sons[0]
                    if s_idx in anc_info:
                        s_str_s,s_inside_lsc = anc_info[s_idx]
                    else:
                        if c_idx not in ancestor_idxs:
                            ancestor_idxs.append(c_idx)
                        early_stop = True
                        break
                        
                    new_lsc = s_inside_lsc + edge_lsc
                    #print s_str_s,rhs
                    if new_lsc>max_lsc:
                        max_str_s = s_str_s + rhs[1:]
                        max_lsc = new_lsc
                        max_idx = s_idx
            try:
                anc_info[c_idx] = (max_str_s,max_lsc)
            except UnboundLocalError:
                if not early_stop:
                    print self.__nodes__[c_idx]
                    sys.exit()
            #print c_idx,max_idx,anc_info[c_idx]
            #print "-----------------------"

        del anc_info[n_idx]
        return anc_info
    #---------------------------------------------------

    #---------------------------------------------------
    # return a list with the best matching nodes
    def __searchBestEcTranslation__(self, isles_s):
        sys.stderr.write("# Searching for best derivation ... ")
        init_time = time.time()
        if len(isles_s)==0:
            isles_s = ['<s>']
        
        # backtracking to obtain best set of nodes
        #print "------------"
        #print "Isles:",isles_s
        valid_nodes = {}
        for n_idx in sorted(self.__nodes__):
            valid_nodes[n_idx] = (tuple(self.__nodes__[n_idx].getCoveredString().strip().split()),self.__nodes__[n_idx].getInsideLogScore())
            # if len(self.__nodes__[n_idx].getParents())>0:
            #     valid_nodes[n_idx] = (tuple(self.__nodes__[n_idx].getCoveredString().strip().split()),self.__nodes__[n_idx].getInsideLogScore())

        nodes_list = []
        first_segm = True
        segm_list = [ segm.strip().split() for segm in " ".join(isles_s).strip().split("<+>") if len(segm.strip())>0 ]
        stack=[]
        segm_idx = 0
        segm_best = 1
        while segm_idx < len(segm_list):
            segm_s = segm_list[segm_idx]
            (ec_lsc,itp_lsc,base_node,base_node_str),still_more_nodes = self.__searchNbestNodeMatchRestricted__(segm_s, segm_best, valid_nodes, first_segm)
            bn_ancestors = self.__ancestors__(base_node,base_node_str,segm_s)
            bn_valid_nodes = {}
            for n_idx in bn_ancestors:
                if n_idx in valid_nodes:
                    bn_valid_nodes[n_idx] = bn_ancestors[n_idx]

            #print segm_s,base_node,len(bn_ancestors),len(bn_valid_nodes),(len(segm_list)-segm_idx-1),still_more_nodes
            #print base_node_str
            #print sorted(bn_ancestors)
            #print ec_lsc,itp_lsc
            #print self.__nodes__[base_node]
            #print bn_valid_nodes
            
            while len(bn_valid_nodes) < (len(segm_list)-segm_idx-1) and len(valid_nodes)>segm_best and still_more_nodes and segm_best<self.__max_backtrack_iters__: 
                # dejamos al menos tantos nodos como segmentos quedan
                segm_best+=1
                (ec_lsc,itp_lsc,base_node,base_node_str),still_more_nodes = self.__searchNbestNodeMatchRestricted__(segm_s, segm_best, valid_nodes, first_segm)
                bn_ancestors = self.__ancestors__(base_node,base_node_str,segm_s)
                bn_valid_nodes = {}
                for n_idx in bn_ancestors:
                    if n_idx in valid_nodes:
                        bn_valid_nodes[n_idx] = bn_ancestors[n_idx]

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
                #print "\nBN:",base_node,base_node_str
                heads = [n_idx for n_idx in self.__nodes__ if len(self.__nodes__[n_idx].getParents())==0]
                if base_node in heads:
                    self.__max_backtrack_iters__ = 2
                    timestamp = time.time()-init_time
                    sys.stderr.write(" Done ( "+str(timestamp)+" s.)\n") 
                    return ec_lsc," ".join(base_node_str).replace("|||","")
                    
                max_lsc = float("-inf")
                max_string = None
                for h_idx in heads:
                    if h_idx in valid_nodes:
                        #print "H:",h_idx, valid_nodes[h_idx]
                        out_string,out_ec_lsc =valid_nodes[h_idx]
                        if out_ec_lsc > max_lsc:
                            max_lsc = out_ec_lsc
                            max_string = out_string
                #print max_lsc,max_string
                #sys.exit()
                self.__max_backtrack_iters__ = 2
                timestamp = time.time()-init_time
                sys.stderr.write(" Done ( "+str(timestamp)+" s.)\n")        
                return max_lsc," ".join(max_string).replace("|||","")
    #---------------------------------------------------


    #---------------------------------------------------
    # return best translation that completes user isles        
    def getTranslation(self, isles_s):
        step_lsc,next_covered_string = self.__searchBestEcTranslation__(isles_s)
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
def user(tra_s, ref_s, mapi):
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
    
    # calcular prefijo
    common_prefix_s = []
    for w_pos in range(min(len(ref_s),len(tra_s))):
        if ref_s[w_pos] == tra_s[w_pos]:
            common_prefix_s.append(ref_s[w_pos])
        else:
            break
    

    isles_limited_effort_s = common_prefix_s[:]
    if len(common_prefix_s)<len(ref_s) and len(common_prefix_s) < len(isles) and isles[len(common_prefix_s)]=="<+>":
        isles_limited_effort_s.append(ref_s[len(common_prefix_s)])
             
    skipped_first_isle = False
    used_ma = 0
    #end_interaction = True
    for w_pos in range(len(isles)):
        w = isles[w_pos]
        if w=="<+>" or w_pos==len(common_prefix_s):
            skipped_first_isle=True
        if skipped_first_isle and used_ma<=mapi:
            isles_limited_effort_s.append(w)
            if w!="<+>":
                used_ma += 1
            else:
                end_interaction = False
    if len(isles_limited_effort_s)<len(ref_s):
        end_interaction = False

    #print end_interaction
    #print common_prefix_s
    #print isles_limited_effort_s
    #print ref_s
    user_stroke_pos = min(user_stroke_pos,len(isles_limited_effort_s)-1)
    if isles_limited_effort_s[-1]!="<+>":
        isles_limited_effort_s.append("<+>")
        
    #return isles,user_feedback,end_interaction,mouse_actions,strokes,user_stroke_pos
    return isles_limited_effort_s,user_feedback,end_interaction,mouse_actions,strokes,user_stroke_pos
###############################################################    
###############################################################



###############################################################
###############################################################
##   MAIN entry to the program
###############################################################
###############################################################
if len(sys.argv)!=7:
    sys.stderr.write("USAGE: "+sys.argv[0]+" <wordgraphFile> <source> <reference> <err_w> <err_p> <mouse-actions-per-iteration>\n")
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


mapi = int(sys.argv[6])
if mapi<0:
    mapi = 0
    sys.stderr.write("# Mouse-actions per iteration rounded to 0\n")

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

    if s_idx<9:
        continue

    user_isles_s = []
    strokes = 0
    while True:
        ec_lsc,itp_lsc,out = hg.getTranslation(user_isles_s)
        tra_s = out.replace("|UNK|UNK|UNK","").replace("<s>","").replace("</s>","").strip().split()

        user_isles_s,user_feedback,end_interaction,ma,ws,user_stroke_pos = user(tra_s, ref_s, mapi)
        strokes += ws

        # output trace
        timestamp = time.time()-init_time
        #sys.stderr.write("Tra ( "+str(timestamp)+" ): "+" ".join([tra_s[pos]+"<"+user_feedback[pos]+">" for pos in range(len(tra_s))])+"\n")
        sys.stderr.write("TRA "+str(s_idx)+" ( "+str(timestamp)+" ): "+" ".join(tra_s)+" ||| "+str(ec_lsc)+" ("+str(itp_lsc)+")\n")
        
        aux_out = user_isles_s[:]
        if user_stroke_pos:
            aux_out[user_stroke_pos] = "["+aux_out[user_stroke_pos]+"]"
        sys.stderr.write("# ISLE: "+" ".join(aux_out)+"\n")
        
        #sys.exit()
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
