#! /usr/bin/pypy

import sys,time,re
#import Levenshtein
from math import log10 as log
from math import factorial as fact


###################################################################################
# CLASS Node
# Represents a node in the hypergraph
###################################################################################
class Node:
    #---------------------------------------------------
    def __init__(self, idx, pos, out, rhs, sons, edge_lsc, inside_lsc):
        self.__topologicPosition__ = pos
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
        output = "H: "+str(self.__idx__)+" ("+str(self.__topologicPosition__)+") => \n"
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
    # returns node topologic position
    def getPos(self):
        return self.__topologicPosition__
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
        self.__ec_cache__ = {}

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
            position = len(self.__nodes__)
            covered_string = self.__stringFromRhs__(rhs,sons)
            new_node = Node(idx, position, covered_string, rhs, sons, edge_lsc, inside_lsc)
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
    # Returnt vector with hyp idx sorted topologically 
    def __hypothesesByTopologicOrder__(self):
        aux = sorted([(self.__nodes__[n_idx].getPos(),n_idx) for n_idx in self.__nodes__])
        return [x[1] for x in aux]
    #---------------------------------------------------

    # #---------------------------------------------------
    # # compute EC score
    # def __ecLogScore__(self,s,r):
    #     # if (s,r) in self.__ec_cache__:
    #     #     return self.__ec_cache__[s,r]

    #     n = len(r)
    #     d = Levenshtein.distance(r,s)
    #     d = min(d,n)
    #     err_lsc = d*log(self.err_p) + (n-d)*log(1.0-self.err_p) + log(fact(n))-(log(fact(d))+log(fact(n-d)))
    #     #self.__ec_cache__[s,r] = err_lsc
    #     return err_lsc
    # #---------------------------------------------------

    # #---------------------------------------------------
    # # return ec log score and ec string
    # def __bestEcLogScore__(self, isl, full_hyp):
    #     full_hyp_s = full_hyp.strip().split()
    #     best_match_lsc = float("-inf")
    #     best_match = None
    #     try:
    #         min_match_pos = full_hyp_s.index("|||")+1
    #         for ini_pos in range(min_match_pos,len(full_hyp_s)):
    #             for end_pos in range(ini_pos+1,len(full_hyp_s)+1):
    #                 candidate_match = " ".join(full_hyp_s[ini_pos:end_pos])
    #                 #print ini_pos,end_pos,candidate_match
    #                 ec_lsc = self.__ecLogScore__(isl,candidate_match)
    #                 if ec_lsc>best_match_lsc:
    #                     best_match_lsc = ec_lsc
    #                     best_match = (ini_pos,end_pos)
    #     except ValueError:
    #         ini_pos = 0
    #         for end_pos in range(ini_pos+1,len(full_hyp_s)+1):
    #             candidate_match = " ".join(full_hyp_s[ini_pos:end_pos])
    #             #print ini_pos,end_pos,candidate_match
    #             ec_lsc = self.__ecLogScore__(isl,candidate_match)
    #             if ec_lsc>best_match_lsc:
    #                 best_match_lsc = ec_lsc
    #                 best_match = (ini_pos,end_pos)
        
    #     if best_match:
    #         ini,end=best_match
    #         #print best_match
    #         new_ec_string = full_hyp_s[:ini]+[isl+" |||"]+full_hyp_s[end:]
    #         return best_match_lsc," ".join(new_ec_string)
    # #---------------------------------------------------


    #---------------------------------------------------
    # Compute best ec match and score
    # TODO: efficient segment match
    def __ecMatch__(self, seq, ref):
        oneago = None
        thisrow = range(1, len(ref) + 1) + [0]
        for x in xrange(len(seq)):
            twoago, oneago, thisrow = oneago, thisrow, [0] * len(ref) + [x + 1]
            for y in xrange(len(ref)):
                delcost = oneago[y] + 1
                addcost = thisrow[y - 1] + 1
                subcost = oneago[y - 1] + (seq[x] != ref[y])
                thisrow[y] = min(delcost, addcost, subcost)
        #print seq
        #print ref
        #print thisrow
        #return thisrow[len(ref) - 1],len(ref)
        thisrow.pop() # eliminate last element
        n = thisrow.index(min(thisrow))+1
        d = thisrow[n-1]
        d = min(d,n)
        err_lsc = d*log(self.err_p) + (n-d)*log(1.0-self.err_p) + log(fact(n))-(log(fact(d))+log(fact(n-d)))
        return err_lsc,n
    #---------------------------------------------------     

    #---------------------------------------------------
    # return ec log score and ec string
    def __bestEcLogScore__(self, isl, full_hyp):
        full_hyp_s = full_hyp.strip().split()
        isl_s = isl.strip().split()
        try:
            min_match_pos = full_hyp_s.index("|||")+1
            candidate_match_s = full_hyp_s[min_match_pos:]
            # reverse suffix matching
            ec_lsc,ec_match_len = self.__ecMatch__(isl_s[::-1],candidate_match_s[::-1])
            best_match = ((len(full_hyp_s)-ec_match_len),len(full_hyp_s))
        except ValueError:
            candidate_match_s = full_hyp_s
            ec_lsc,ec_match_len = self.__ecMatch__(isl_s,candidate_match_s)
            best_match = (0,ec_match_len)
        
        if best_match:
            ini,end=best_match
            #print isl_s
            #print full_hyp_s
            #print best_match
            new_ec_string = full_hyp_s[:ini]+[isl+" |||"]+full_hyp_s[end:]
            return ec_lsc," ".join(new_ec_string)
    #---------------------------------------------------
    
    #---------------------------------------------------
    # return best translation that completes user isles
    # dynamic programming over nodes
    def getEcTranslation(self, isles_s):
        ordered_nodes = self.__hypothesesByTopologicOrder__()
        #print isles_s
        isles = [x.strip() for x in ("<s> "+" ".join(isles_s)).strip().split("<+>") if len(x.strip())>0]
        #print isles
        N = len(isles)
        heads = dict([(h_idx,True) for h_idx in self.__nodes__ if len(self.__nodes__[h_idx].getParents())==0])

        Q={}
        # base case, only one node in WG
        n_idx = 0
        hyp = self.__nodes__[n_idx]
        Q[n_idx,-1]=(hyp.getCoveredString(), hyp.getInsideLogScore(), hyp.getInsideLogScore()) # no cover
        isl = isles[0]
        err_lsc,new_ec_str = self.__bestEcLogScore__(isl,hyp.getCoveredString())
        Q[n_idx,0]=(new_ec_str, hyp.getInsideLogScore()+err_lsc, hyp.getInsideLogScore()) # cover first isle

        #print Q[n_idx,-1]
        #print Q[n_idx,0]

        # general recursion
        assert ordered_nodes.pop(0)==0 # delete base case
        for n_idx in ordered_nodes:
            hyp = self.__nodes__[n_idx]
            hyp_sons = hyp.getSons()
            Q[n_idx,-1] = (hyp.getCoveredString(), hyp.getInsideLogScore(), hyp.getInsideLogScore()) # no cover
            #print n_idx,-1,Q[n_idx,-1]
            for num_isle in range(N):
                for rhs,sons,edge_lsc in hyp_sons:
                    s_idx = sons[0]
                    if (s_idx,num_isle-1) in Q:
                        s_str,s_lsc,_ = Q[s_idx,num_isle-1]
                        new_str = s_str+" "+" ".join(rhs[1:])
                        #print new_str
                        err_lsc,new_ec_str = self.__bestEcLogScore__(isles[num_isle],new_str)
                        cur_lsc = hyp.getInsideLogScore()+err_lsc
                        if (n_idx,num_isle) not in Q or Q[n_idx,num_isle][1]<cur_lsc:
                            Q[n_idx,num_isle] = (new_ec_str, cur_lsc, hyp.getInsideLogScore())
                            #print "F ->",s_idx,num_isle-1,Q[s_idx,num_isle-1]
                            #print "T ->",n_idx,num_isle,Q[n_idx,num_isle]
                                
        best_ec_lsc = float("-inf")
        best_ec_str = None
        for h_idx in heads:
            if (h_idx,N-1) in Q and Q[h_idx,N-1][1]>best_ec_lsc:
                best_ec_str,best_ec_lsc,best_itp_lsc = Q[h_idx,N-1]
                #print "Head:",h_idx,N-1,Q[h_idx,N-1]
        #sys.exit()
        return best_ec_lsc,best_itp_lsc,best_ec_str.replace("|||","")
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

    if s_idx<0:
        continue
    # if s_idx>1:
    #     sys.exit()

    user_isles_s = []
    strokes = 0
    while True:
        ec_lsc,itp_lsc,out = hg.getEcTranslation(user_isles_s)
        tra_s = out.replace("|UNK|UNK|UNK","").replace("<s>","").replace("</s>","").strip().split()

        #print tra_s
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
