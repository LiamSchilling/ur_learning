"""A class defining the Finite State Transducer.
Copyright (C) 2019 Alena Aksenova.
Copyright (C) 2026 William Schilling.

This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 3 of the License, or (at your
option) any later version.

Modified by William (Liam) Schilling:

Implemented core finite-state operations,
taking `FST` to be a general (potentially nondeterministic) finite-state transducer
that accepts a relation over strings. Most notably, added
`trim`, `expand_inputs`, `expand_final`, `invert`, `concatenate`, `kleene_closure`,
`prefix_closure`, `union`, `intersect`, `compose`, and `determinize`.

These functions assume the following `FST` representation invariants, stated as type annotations:
    Q (Annotated[list[str], "no duplicates"])
    Sigma (Annotated[list[Annotated[str, "length==1"]], "no duplicates"])
    Gamma (Annotated[list[Annotated[str, "length==1"]], "no duplicates"])
    qe (Annotated[str, "in Q"])
    E (Annotated[list[
            Annotated[str, "in Q"],
            Annotated[str, "alphabet is Sigma"],
            Annotated[str, "alphabet is Gamma"],
            Annotated[str, "in Q"]
        ], "no duplicates"])
    stout (dict[
            Annotated[str, "in Q"],
            Annotated[str, "alphabet is Gamma"]
        ])
As an additional note, we take states that are not keys of `stout` to be the rejecting states.
This is different from the `DFA` class in `dfa_object.py`, which marks accepting states separately.

The functions explicitly track the following useful FST properties.
The docstrings declare which are ensured by and which are invariants of the implementations.
- Trimmedness: Every state and transition is traversed by some accepting run
  (except in the edge case of the empty FST, which may only have one state and no transitions).
  Because of this edge case, some functions must take special care to be trimmedness-preserving.
- Final-output emptiness: Every final output (values of `stout`) is the empty string.
- Input-string expansion: The input string of every transition is either a character or empty.
- Determinism: The input string of every transition is a character,
  and for each state, every character is the input string of no more than one outgoing transition.
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
    
    def transition(self, q, w):
        """Traverses from the state `q` according to the string `w`,
        and returns the resulting state.
        Returns `None` if a missing transition is encountered.

        Args:
            q: the start state.
            w (str): a string to read.

        Returns:
            the state reached by `w` from `q`, or `None`.
        """
        if self.Q == None:
            raise ValueError("The transducer needs to be constructed.")
        
        for c in w:
            moved = False
            for tr in self.E:
                if tr[0] == q and tr[1] == c:
                    q = tr[3]
                    break
            if not moved:
                return None
        
        return q

    def copy_fst(self):
        """Produces a deep copy of the current FST.

        Returns:
            T (FST): a copy of the current FST.
        """
        T = FST()
        T.Q = deepcopy(self.Q)
        T.Sigma = deepcopy(self.Sigma)
        T.Gamma = deepcopy(self.Gamma)
        T.qe = deepcopy(self.qe)
        T.E = deepcopy(self.E)
        T.stout = deepcopy(self.stout)

        return T

    def fresh_state(self, name_prefix):
        """Finds a name that is not the name of a state already in the FST.
        Specifically, returns the first available name of the form `f"{name_prefix}.{i}"`
        where `i` is a nonnegative integer.

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
        the string representations of the arguments do not contain `;`, `<`, or `>`,
        except for from previous invokations of this function.

        It is important that the client adhere to this condition in their FSTs,
        or else the state encodings produced by functions in our library
        could violate the "no duplicates" invariant of the state set.

        Args:
            *args: information to be encoded as a state name.

        Return:
            str: a name that encodes the values of the arguments.
        """
        return f"<{args.map(str).join(";")}>"
    
    def is_trim_but_empty(F):
        """A helper function that checks
        whether an FST is the edge case of the trimmedness condition.
        That is, the empty FST with one rejecting state and no transitions.

        Args:
            F (FST): the FST to be checked.
        
        Returns:
            bool: whether the FST has one rejecting state and no transitions.
        """
        return len(F.Q) == 1 and len(F.E) == 0 and len(F.stout) == 0
    
def new_rejector(Sigma, Gamma):
    """Creates an FST that rejects every string pair.
    
    Ensures:
        trimmedness
        final-output emptiness
        input-string expansion
        determinism

    Args:
        Sigma (list): the input alphabet.
        Gamma (list): the output alphabet.
    
    Returns:
        FST: the rejector FST.
    """
    # initialize the new FST
    F = FST(Sigma, Gamma)
    F.Q, F.E, F.qe, F.stout = ["q"], [], "q", {}

    return F

def new_acceptor(Sigma, Gamma):
    """Creates an FST that accepts every string pair.
    
    Ensures:
        trimmedness
        final-output emptiness
        input-string expansion

    Args:
        Sigma (list): the input alphabet.
        Gamma (list): the output alphabet.
    
    Returns:
        FST: the acceptor FST.
    """
    # initialize the new FST
    F = FST(Sigma, Gamma)
    F.Q, F.E, F.qe, F.stout = ["q"], [], "q", {"q" : ""}

    # add transitions that allow writing any character to input or output
    for c in Sigma:
        F.E.append(["q", c, "", "q"])
    for c in Gamma:
        F.E.append(["q", "", c, "q"])

    return F

def trim_inaccessible(F):
    """Removes states and transitions from the FST
    that are not accessible from the initial state.

    Invariants:
        trimmedness
        final-output emptiness
        input-string expansion
        determinism

    Args:
        F (FST): the original FST.

    Returns:
        FST: the trimmed FST.
    """
    # initialize the new FST
    G = FST(deepcopy(F.Sigma), deepcopy(F.Gamma))
    Q_set, E_set, G.qe, G.stout = set(), set(), F.qe, {}

    # perform a breadth-first traversal of the original FST from the initial state
    worklist = Queue()
    worklist.put(F.qe)
    while not worklist.empty():
        curr_q = worklist.pop()
        if curr_q not in Q_set:
            Q_set.insert(curr_q)
            for [q, u, v, q_] in F.E:
                if curr_q == q:
                    E_set.insert([q, u, v, q_])
                    worklist.put(q_)

    # copy over the final outputs of the states that remain
    for q, w in F.stout:
        if q in Q_set:
            G.stout[q] = w

    G.Q, G.E = list(Q_set), list(E_set)
    return G

def trim_useless(F):
    """Removes states and transitions from the FST
    from which no accepting state is accessible,
    except for the initial state, which is not allowed to be removed.

    Invariants:
        trimmedness
        final-output emptiness
        input-string expansion
        determinism

    Args:
        F (FST): the original FST.

    Returns:
        FST: the trimmed FST.
    """
    # initialize the new FST
    G = FST(deepcopy(F.Sigma), deepcopy(F.Gamma))
    Q_set, E_set, G.qe, G.stout = set(), set(), F.qe, {}

    # perform a breadth-first traversal of the original FST from the accepting states
    worklist = Queue()
    for q in F.stout.keys():
        worklist.put(q)
    while not worklist.empty():
        curr_q_ = worklist.pop()
        if curr_q_ not in Q_set:
            Q_set.insert(curr_q_)
            for [q, u, v, q_] in F.E:
                if curr_q_ == q_:
                    E_set.insert([q, u, v, q_])
                    worklist.put(q)

    # add back the initial state if it was not traversed already
    if G.qe not in Q_set:
        Q_set.insert(G.qe)

    # copy over the final outputs of the states that remain
    for q, w in F.stout:
        if q in Q_set:
            G.stout[q] = w

    G.Q, G.E = list(Q_set), list(E_set)
    return G

def trim(F):
    """Removes states and transitions from the FST
    that are never traversed by an accepting run.

    Ensures:
        trimmedness

    Invariants:
        final-output emptiness
        input-string expansion
        determinism

    Args:
        F (FST): the original FST.

    Returns:
        FST: the trimmed FST.
    """
    return trim_useless(trim_inaccessible(F))

def expand_inputs(F):
    """Expands transitions with multi-character input strings
    into non-accepting chains of transitions with single-character input strings.

    Ensures:
        input-string expansion

    Invariants:
        trimmedness
        final-output emptiness
        determinism

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
    # of the form `[<q; w>, c, "", <q; wc>]`, where `wc` is an incomplete prefix of `u`,
    # along with the completing transition `[<q; w>, c, v, <q'; "">]`, where `wc` equals `u`.
    for q in F.Q:
        Q_set.insert(FST.encode_state(q, ""))
    for [q, u, v, q_] in F.E:
        for i in range(1, len(u)):
            Q_set.insert(FST.encode_state(q, u[:i]))
            E_set.insert([FST.encode_state(q, u[:i-1]), u[i-1], "", FST.encode_state(q, u[:i])])
        E_set.insert([FST.encode_state(q, u[:-1]), u[-1:], v, FST.encode_state(q_, "")])

    # copy over the final outputs
    for q, w in F.stout:
        G.stout[FST.encode_state(q, "")] = w

    G.Q, G.E = list(Q_set), list(E_set)
    return G

def expand_final(F):
    """Expands final states with nonempty output strings
    into a non-accepting state with a transition to a new accepting state.

    Ensures:
        final-output emptiness

    Invariants:
        trimmedness
        input-string expansion

    Args:
        F (FST): the original FST.
    
    Returns:
        FST: an FST that accepts the same relation but has no nonempty final outputs.
    """
    # initialize the new FST
    G = FST(deepcopy(F.Sigma), deepcopy(F.Gamma))
    G.Q, G.E, G.qe, G.stout = deepcopy(F.Q), deepcopy(F.E), F.qe, {}

    # account for nonempty final outputs by turning them into transitions to new accepting states,
    # if empty then just copy the final output verbatim
    for q, w in F.stout:
        if w == "":
            G.stout[q] = ""
        else:
            G.Q.append(q_ := G.fresh_state_name(q))
            G.E.append([q, "", w, q_])
            G.stout[q_] = ""

    return G

def invert(F):
    """Given an FST that accepts the relation `R`,
    returns an FST that accepts the relation `{ (u, v) | (v, u) ∈ R }`.

    Ensures:
        final-output emptiness

    Invariants:
        trimmedness

    Args:
        F (FST): the original FST.

    Returns:
        FST: the inverted FST.
    """
    # we need final outputs to be empty because the FST class does not support final inputs
    F = expand_final(F)

    # initialize the new FST
    G = FST(deepcopy(F.Sigma), deepcopy(F.Gamma))
    G.Q, G.E, G.qe, G.stout = deepcopy(F.Q), [], F.qe, deepcopy(F.stout)

    # copy over the transitions with swapped input an output strings
    for [q, u, v, q_] in F.E:
        G.E.append([q, v, u, q_])

    return G

def concatenate(F, G):
    """Given FSTs that accept the relations `RF` and `RG`, respectively,
    returns an FST that accepts the relation `RF · RG`.
    That is, the relation of all string pairs that are the result of
    concatenating a string pair from `RF` to a string pair from `RG`.

    Invariants:
        trimmedness
        final-output emptiness
        input-string expansion

    Args:
        F (FST): the left-hand original FST.
        G (FST): the right-hand original FST.

    Returns:
        FST: the concatenation FST.
    """
    # we need final outputs of the first machine to be empty
    # so that we do not miss output upon traversal to the next machine
    F = expand_final(F)

    # initialize the new FST
    H = FST(list(set(F.Sigma).union(G.Sigma)), list(set(F.Gamma).union(G.Gamma)))
    H.Q, H.E, H.qe, H.stout = [], [], FST.encode_state("LEFT", F.qe), {}

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

    # for every final state,
    # create an epsilon transition to nondeterministically begin running the next machine
    for qf in F.stout.keys():
        H.E.append([FST.encode_state("LEFT", qf), "", "", FST.encode_state("RIGHT", G.qe)])
    
    # cope over the final transitions of the other machine
    for qg, w in G.stout:
        H.stout[FST.encode_state("RIGHT", qg)] = w

    return H

def kleene_closue(F):
    """Given an FST that accepts the relation `R`,
    returns an FST that accepts the relation `R*`.
    That is, the relation of all string pairs that are the result of
    concatenating many string pairs from `R`.

    Ensures:
        final-output emptiness
    
    Invariants:
        trimmedness
        input-string expansion

    Args:
        F (FST): the original FST.
    
    Returns:
        FST: the kleene-closure FST.
    """
    # we need final outputs to be empty
    # so that we do not miss output upon traversal back to the initial state
    F = expand_final(F)

    # initialize the new FST
    G = FST(deepcopy(F.Sigma), deepcopy(F.Gamma))
    G.Q, G.E, G.qe, G.stout = deepcopy(F.Q), deepcopy(F.E), F.qe, deepcopy(F.stout)

    # for every final state,
    # create an epsilon transition to nondeterministically return to the initial state
    for q in G.stout.keys():
        tr = [q, "", "", G.qe]
        if tr not in G.E:
            G.E.append(tr)

    return G

def prefix_closure(F):
    """Given an FST whose domain is the language `L`,
    returns an FST whose domain is the language `prefixes(L)`.
    How the function treats FST outputs is currently underspecified, though we guarantee that
    the relation accepted by the original FST is a subset of the relation accepted by the new FST.

    Ensures:
        trimmedness
        input-string expansion

    Invariants:
        final-output emptiness
        determinism

    Args:
        F (FST): the original FST.

    Returns:
        FST: the prefix-closure FST.
    """
    # construct an FST where exactly the prefix closure of the original domain has valid runs
    F = expand_inputs(trim(F))

    # mark every state as accepting,
    # unless the FST is just one rejecting state, which is the empty FST edge case
    if not F.is_trim_but_empty():
        for q in F.Q:
            if q not in F.stout:
                F.stout[q] = ""

    return F

def union(F, G):
    """Given FSTs that accept the relations `RF` and `RG`, respectively,
    returns an FST that accepts the relation `RF ∪ RG`.

    Invariants:
        trimmedness
        final-output emptiness
        input-string expansion

    Args:
        F (FST): the left-hand original FST.
        G (FST): the right-hand original FST.

    Returns:
        FST: the union FST.
    """
    # initialize the new FST
    H = FST(list(set(F.Sigma).union(G.Sigma)), list(set(F.Gamma).union(G.Gamma)))
    H.Q, H.E, H.qe, H.stout = [], [], FST.encode_state("LEFT", F.qe), {}

    # create an epsilon transition to nondeterministically choose between running `F` and `G`
    H.E.append([FST.encode_state("LEFT", F.qe), "", "", FST.encode_state("RIGHT", G.qe)])

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

    Ensures:
        final-output emptiness

    Invariants:
        input-string expansion

    Args:
        F (FST): the left-hand original FST.
        G (FST): the right-hand original FST.

    Returns:
        FST: the intersection FST.
    """
    # expanding final outputs beforehand makes this construction far easier,
    # but it also means that determinism is not an invariant,
    # whereas it would be in a more robust implementation
    F, G = expand_final(F), expand_final(G)

    # initialize the new FST
    H = FST(list(set(F.Sigma).union(G.Sigma)), list(set(F.Gamma).union(G.Gamma)))
    Q_set, E_set, H.stout = set(), set(), {}
    H.qe = FST.encode_state(F.qe, G.qe, ("", ""), ("", ""))

    # perform a breadth-first traversal of the original FSTs from the accepting states
    worklist = Queue()
    worklist.put(F.qe, G.qe, ("", ""), ("", ""))
    while not worklist.empty():
        (curr_qf, curr_qg, (curr_uf, curr_vf), (curr_ug, curr_vg)) = worklist.pop()
        new_q = FST.encode_state(curr_qf, curr_qg, (curr_uf, curr_vf), (curr_ug, curr_vg))
        if new_q not in Q_set:
            Q_set.insert(new_q)
            for [qf, uf, vf, qf_] in F.E:
                for [qg, ug, vg, qg_] in G.E:
                    states_match = curr_qf == qf and curr_qg == qg
                    f_buffers_match = uf.startswith(curr_uf) and vf.startswith(curr_vf)
                    g_buffers_match = ug.stateswith(curr_ug) and vg.startswith(curr_vg)
                    if states_match and f_buffers_match and g_buffers_match:
                        uf_suff, vf_suff = uf[len(curr_uf):], vf[len(curr_vf):]
                        ug_suff, vg_suff = ug[len(curr_ug):], vg[len(curr_vg):]
                        if uf_suff == ug_suff and vf_suff == vg_suff:
                            new_q_ = FST.encode_state(qf_, qg_, ("", ""), ("", ""))
                            new_u, new_v = uf_suff, vf_suff
                        elif uf_suff.startswith(ug_suff) and vf_suff.startswith(vg_suff):
                            uf_buff, vf_buff = uf_suff[len(ug_suff):], vf_suff[len(vg_suff):]
                            new_q_ = FST.encode_state(qf, qg_, (uf_buff, vf_buff), ("", ""))
                            new_u, new_v = ug_suff, vg_suff
                        elif ug_suff.startswith(uf_suff) and vg_suff.startswith(vf_suff):
                            ug_buff, vg_buff = ug_suff[len(uf_suff):], vg_suff[len(vf_suff):]
                            new_q_ = FST.encode_state(qf_, qg, ("", ""), (ug_buff, vg_buff))
                            new_u, new_v = uf_suff, vf_suff
                        E_set.insert([new_q, new_u, new_v, new_q_])
                        worklist.put(new_q_)

    # copy over the shared final states
    for qf, _ in F.stout:
        for qg, _ in G.stout:
            new_q = FST.encode_state(qf, qg, ("", ""), ("", ""))
            if new_q in Q_set:
                H.stout[new_q] = ""

    H.Q, H.E = list(Q_set), list(E_set)
    return H

def compose(F, G):
    """Given FSTs that accept the relations `RF` and `RG`, respectively,
    returns an FST that accepts the relation `{ (u, v) | ∃ w, (u, w) ∈ RG ∧ (w, v) ∈ RF }`.
    In the special case that `RF` and `RG` are both subsequential functions
    (which is guaranteed if both original FSTs are deterministic),
    this has the effect of typical function composition.

    Ensures:
        final-output emptiness

    Invariants:
        input-string expansion

    Args:
        F (FST): the left-hand (second applied) original FST.
        G (FST): the right-hand (first applied) original FST.

    Returns:
        FST: the composition FST.
    """
    # expanding final outputs beforehand makes this construction far easier,
    # but it also means that determinism is not an invariant,
    # whereas it would be in a more robust implementation
    F, G = expand_final(F), expand_final(G)

    # initialize the new FST
    H = FST(F.Sigma, G.Gamma)
    Q_set, E_set, H.stout = set(), set(), {}
    G.qe = FST.encode_state(F.qe, G.qe, "")

    # perform a breadth-first traversal of the original FSTs from the accepting states
    worklist = Queue()
    worklist.put(F.qe, G.qe, "")
    while not worklist.empty():
        (curr_qf, curr_qg, curr_uf) = worklist.pop()
        new_q = FST.encode_state(curr_qf, curr_qg, curr_uf)
        if new_q not in Q_set:
            Q_set.insert(new_q)
            for [qg, ug, vg, qg_] in G.E:
                if curr_qg == qg:

                    # perform an inner breadth-first traversal of states reached by `curr_uf + vg`
                    visited = set()
                    inner_worklist = Queue()
                    inner_worklist.put(curr_qf, curr_uf + vg, "")
                    while not inner_worklist.empty():
                        (curr_qf, curr_uf, curr_vf) = inner_worklist.pop()
                        if (curr_qf, curr_uf) not in visited:
                            visited.insert((curr_qf, curr_uf))
                            for [qf, uf, vf, qf_] in F.E:
                                if curr_qf == qf:
                                    if uf.startswith(curr_uf):
                                        if uf == curr_uf:
                                            new_q_ = FST.encode_state(qf_, qg_, "")
                                            new_v = curr_vf + vf
                                        else:
                                            new_q_ = FST.encode_state(qf, qg_, curr_uf)
                                            new_v = curr_vf
                                        E_set.insert([new_q, ug, new_v, new_q_])
                                        worklist.put(new_q_)
                                    if curr_uf.startswith(uf):
                                        inner_worklist.put(qf_, curr_uf[len(uf):], curr_vf + vf)

    # copy over the shared final states
    for qf, _ in F.stout:
        for qg, _ in G.stout:
            new_q = FST.encode_state(qf, qg, "")
            if new_q in Q_set:
                H.stout[new_q] = ""

    H.Q, H.E = list(Q_set), list(E_set)
    return H

def determinize(F):
    """Turns a nondeterministic FST that recognizes a subsequential function
    into a deterministic FST that recognizes the same function.
    A deterministic FST has only single-character input strings,
    and for each state, at most one outgoing transition with every input string.

    Ensures:
        ?

    Invariants:
        ?

    Args:
        F (FST): the original functional FST.
    
    Returns:
        FST: an FST that accepts the same function but is deterministic.
    """
    raise NotImplementedError
