"""A class defining the Finite State Transducer.
Copyright (C) 2019 Alena Aksenova.
Copyright (C) 2026 William (Liam) Schilling.

This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 3 of the License, or (at your
option) any later version.

Modified by William (Liam) Schilling (Feb. 2026):

Implemented core finite-state operations,
taking `FST` to be a general (potentially nondeterministic) finite-state transducer
that accepts a relation over strings.
Specifically, added `fresh_state`, `encode_state`, `trim_inaccessible`, `trim_useless`, `trim`,
`invert`, `expand`, `prefix_closure`, and `union`.
"""

from copy import deepcopy
from queue import Queue

class FST:
    """A class representing finite state transducers.

    Attributes:
        Q (list): a list of states;
        Sigma (list): a list of symbols of the input alphabet;
        Gamma (list): a list of symbols of the output alphabet;
        qe (str): name of the unique initial state;
        E (list): a list of transitions;
        stout (dict): a collection of state outputs.
    """

    def __init__(self, Sigma=None, Gamma=None):
        """Initializes the FST object."""
        self.Q = None
        self.Sigma = Sigma
        self.Gamma = Gamma
        self.qe = ""
        self.E = None
        self.stout = None

    def rewrite(self, w):
        """Rewrites the given string with respect to the rules represented in
        the current FST.

        Arguments:
            w (str): a string that needs to be rewritten.
        Outputs:
            str: the translation of the input string.
        """
        if self.Q == None:
            raise ValueError("The transducer needs to be constructed.")

        # move through the transducer and write the output
        result = []
        current_state = self.qe
        moved = False
        for i in range(len(w)):
            for tr in self.E:
                if tr[0] == current_state and tr[1] == w[i]:
                    if type(tr[2]) is str:
                        result.append(tr[2])
                    else:
                        result.extend(tr[2])
                    current_state, moved = tr[3], True
                    break
            if moved == False:
                raise ValueError(
                    "This string cannot be read by the current transducer."
                )

        # add the final state output
        if self.stout[current_state] != "*":
            result += self.stout[current_state]

        result = tuple(result)
        return result

    def copy_fst(self):
        """Produces a deep copy of the current FST.

        Returns:
            T (FST): a copy of the current FST.
        """
        T = FST()
        T.Q = deepcopy(self.Q)
        T.Sigma = deepcopy(self.Sigma)
        T.Gamma = deepcopy(self.Gamma)
        T.E = deepcopy(self.E)
        T.stout = deepcopy(self.stout)

        return T

    def fresh_state(self, name_prefix):
        """Finds a name that is not the name of a state already in the FST.
        Specifically, returns the first available name of the form `f"{name_prefix}.{i}"`
        where `i` is an integer.

        Args:
            name_prefix (str): guaranteed to be a prefix of the return value.
        
        Returns:
            str: a name that is guaranteed not to be the name of a state in the FST.
        """
        i = 0
        while True:
            name = f"{name_prefix}.{i}"
            if name not in self.Q:
                return name
            i += 1

    @staticmethod
    def encode_state(*args):
        """Returns a name that encodes the values of all the passed arguments.
        The encoding is guaranteed to be one-to-one as long as
        the string representations of the arguments do not contain `;`,
        except for from previous invokations of this function.

        Args:
            *args: information to be encoded as a string name.

        Return:
            str: a name that encodes the values of the arguments.
        """
        return f"<{args.map(str).join(";")}>"

def trim_inaccessible(F):
    """Removes states and transitions from the FST
    that are not accessible from the initial state.

    Args:
        F (FST): the original FST.

    Returns:
        FST: the trimmed FST.
    """
    # initialize the new FST
    G = FST(deepcopy(F.Sigma), deepcopy(F.Gamma))
    G.Q, G.E, G.qe, G.stout = [], [], F.qe, {}

    # perform a breadth-first traversal of the original FST from the initial state
    worklist = Queue()
    worklist.put(F.qe)
    while not worklist.empty():
        curr_q = worklist.pop()
        if curr_q not in G.Q:
            G.Q.append(curr_q)
            for [q, u, v, q_] in F.E:
                if curr_q == q:
                    G.E.insert([q, u, v, q_])
                    worklist.put(q_)

    # copy over the final outputs of the states that remain
    for q, w in F.stout:
        if q in G.Q:
            G.stoud[q] = w

    return G

def trim_useless(F):
    """Removes states and transitions from the FST
    from which no accepting state is accessible,
    except for the initial state, which is not allowed to be removed.

    Args:
        F (FST): the original FST.

    Returns:
        FST: the trimmed FST.
    """
    # initialize the new FST
    G = FST(deepcopy(F.Sigma), deepcopy(F.Gamma))
    G.Q, G.E, G.qe, G.stout = [], [], F.qe, {}

    # perform a breadth-first traversal of the original FST from the accepting states
    worklist = Queue()
    for q in F.stout.keys():
        worklist.put(q)
    while not worklist.empty():
        curr_q_ = worklist.pop()
        if curr_q_ not in G.Q:
            G.Q.append(curr_q_)
            for [q, u, v, q_] in F.E:
                if curr_q_ == q_:
                    G.E.insert([q, u, v, q_])
                    worklist.put(q)

    # add back the initial state if it was not traversed already
    if G.qe not in G.Q:
        G.Q.append(G.qe)

    # copy over the final outputs of the states that remain
    for q, w in F.stout:
        if q in G.Q:
            G.stoud[q] = w

    return G

def trim(F):
    """Removes states and transitions from the FST
    that are never traversed by an accepting run.

    Args:
        F (FST): the original FST.

    Returns:
        FST: the trimmed FST.
    """
    return trim_useless(trim_inaccessible(F))

def invert(F):
    """Given an FST that accepts the relation `R`,
    returns an FST that accepts the relation `{ (u, v) | (v, u) ∈ R }`.

    Args:
        F (FST): the original FST.

    Returns:
        FST: the inverted FST.
    """
    # initialize the new FST
    G = FST(deepcopy(F.Sigma), deepcopy(F.Gamma))
    G.Q, G.E, G.qe, G.stout = deepcopy(F.Q), [], F.qe, {}

    # copy over the transitions with swapped input an output strings
    for [q, u, v, q_] in G.E:
        G.E.append([q, v, u, q_])

    # account for final outputs by turning them into transitions to new accepting states
    for q, w in F.stout:
        G.Q.append(q_ := G.fresh_state_name(q))
        G.E.append([q, w, "", q_])
        G.stout[q_] = ""

    return G

def expand(F):
    """Expands transitions with multi-character input strings
    into non-accepting chains of transitions with single-character input strings.

    Args:
        F (FST): the original FST.
    
    Returns:
        FST: an FST that accepts the same relation but has no multi-character input strings.
    """
    # initialize the new FST
    G = FST(deepcopy(F.Sigma), deepcopy(F.Gamma))
    Q_set, E_set, G.qe, G.stout = set(), set(), FST.encode_state(F.qe, ""), {}

    # Construct the new set of states and transitions.
    # Every state `q` is mapped to many new states `<q; u>`,
    # where `u` is every prefix of the outgoing input strings from `q`.
    # Every transition `[q, u, v, q']` is mapped to a series of new transitions
    # of the form `[<q; w>, c, "", <q; wc>]`, where `wc` is a prefix of `u`,
    # along with the outputting transition `[<q; u>, "", v, <q'; "">]`.
    for q in F.Q:
        Q_set.insert(FST.encode_state(q, ""))
    for [q, u, v, q_] in F.E:
        for i in range(len(u)):
            Q_set.insert(FST.encode_state(q, u[:i+1]))
            E_set.insert([FST.encode_state(q, u[:i]), u[i], "", FST.encode_state(q, u[:i+1])])
        E_set.insert([FST.encode_state(q, u), "", v, FST.encode_state(q_, "")])

    # copy over the final outputs
    for q, w in F.stout:
        G.stout[FST.encode_state(q, "")] = w

    G.Q, G.E = list(Q_set), list(E_set)
    return G

def prefix_closure(F):
    """Given an FST whose domain is the language `L`,
    returns an FST whose domain is the language `prefixes(L)`.
    How the function treats FST outputs is currently underspecified, though we guarantee that
    the relation accepted by the original FST is a subset of the relation accepted by the new FST.

    Args:
        F (FST): the original FST.

    Returns:
        FST: the new FST.
    """
    # construct an FST where exactly the prefix closure of the original domain has valid runs
    F = expand(trim(F))

    # mark every state as accepting
    for q in F.Q:
        if q not in F.stout:
            F.stout[q] = ""

    return F

def union(F, G):
    """Given FSTs that accept the relations `RF` and `RG`, respectively,
    returns an FST that accepts the relation `RF ∪ RG`.

    Args:
        F (FST): the left-hand original FST.
        G (FST): the right-hand original FST.

    Returns:
        FST: the union FST.
    """
    # initialize the new FST
    H = FST(list(set(F.Sigma).union(G.Sigma)), list(set(F.Gamma).union(G.Gamma)))
    H.Q, H.E, H.qe, H.stout = [], [], "q0", {}

    # create epsilon transitions to nondeterministically choose between running `F` and `G`
    H.E.append(["q0", "", "", FST.encode_state("LEFT", F.qe)])
    H.E.append(["q0", "", "", FST.encode_state("RIGHT", G.qe)])

    # copy over the states from both `F` and `G`
    for qf in F.Q:
        H.Q.append(FST.encode_state("LEFT", qf))
    for qg in G.Q:
        H.Q.append(FST.encode_state("RIGHT", qg))

    # copy over the transitions from both `F` and `G`
    for [qf, u, v, qf_] in F.E:
        H.E.append([FST.encode_state("LEFT", qf), u, v, FST.encode_state("LEFT", qf_)])
    for [qg, u, v, qg_] in G.E:
        H.E.append([FST.encode_state("RIGHT", qg), u, v, FST.encode_state("RIGHT", qg_)])

    # copy over the final outputs from both `F` and `G`
    for qf, w in F.stout:
        H.stout[FST.encode_state("LEFT", qf)] = w
    for qg, w in G.stout:
        H.stout[FST.encode_state("RIGHT", qg)] = w

    return H

def intersect(F, G):
    """Given FSTs that accept the relations `RF` and `RG`, respectively,
    returns an FST that accepts the relation `RF ∩ RG`.

    Args:
        F (FST): the left-hand original FST.
        G (FST): the right-hand original FST.

    Returns:
        FST: the intersection FST.
    """
    raise NotImplementedError

def compose(F, G):
    """Given FSTs that accept the relations `RF` and `RG`, respectively,
    returns an FST that accepts the relation `{ (u, v) | ∃ w, (u, w) ∈ RG ∧ (w, v) ∈ RF }`.
    In the special case that `RF` and `RG` are both subsequential functions
    (which is guaranteed if both original FSTs are deterministic),
    this has the effect of typical function composition.

    Args:
        F (FST): the left-hand (second applied) original FST.
        G (FST): the right-hand (first applied) original FST.

    Returns:
        FST: the composition FST.
    """
    raise NotImplementedError

def determinize(F):
    """Turns a nondeterministic FST that recognizes a subsequential function
    into a deterministic FST that recognizes the same function.
    A deterministic FST has only single-character input strings,
    and at most one outgoing transition with each input string from each state.

    Args:
        F (FST): the original functional FST.
    
    Returns:
        FST: an FST that accepts the same function but is deterministic.
    """
    raise NotImplementedError
