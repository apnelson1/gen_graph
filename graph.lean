import tactic

open_locale classical 

noncomputable theory 

open set

/-- This is a weird, very 'inclusive' definition of a graph, allowing for directed/undirected edges
  and some more degenerate flavours of edge. Here, `inc ff e` is the set of 'heads' of `e` and 
  `inc tt e` is the set of `tails`. The `well_def` axiom implies that both these sets have size at
  most two, and that if one has size two, they are the same set. This allows for 'free' edges with 
  no ends, 'half-edges' with exactly one end (either the head or the tail), 'loops' with a head and 
  a tail that are equal, 'arcs' with a head and tail that are distinct, and 'edges' with two heads 
  and two tails so that the heads and the tails coincide. These can be thought of as edges directed 
  in both ways, or equivalently as edges directed in neither way. 

  The appearance of edges of all five types can be easily controlled using (data-free) typeclasses.
  This is really nice; it allows both digraphs and undirected graphs to be examples, without
  quotients.
  
  Half edges and free edges do appear in some mathematical contexts, and can be easily forbidden 
  via typeclasses in contexts where they don't make sense. If we just forbid them, we basically 
  get digraphs (where edges can be directed both ways at once). 
  
  If arcs, half-edges and free edges are forbidden, then we get undirected multigraphs with loops. 
  
  If, on top of this, we forbid loops and insist that the 'ends' map is injective, we get simple 
  graphs.
  -/
@[ext] structure graph (V : Type*) (E : Type*) := 
  (inc : bool → E → finset V)
  (well_def : ∀ i e, 2 ≤ (inc i e).card → ∃ (u v : V), u ≠ v ∧ ∀ j, inc j e = ({u,v} : finset V))

namespace graph

variables {V E : Type*} {G : graph V E} {e f : E} {u v w : V}

/-- An edge is `full` if it actually has two ends -/
def is_full (G : graph V E) (e : E) : Prop := ∀ i, (G.inc i e).nonempty

def ends (G : graph V E) (e : E) : finset V := G.inc ff e ∪ G.inc tt e 

/-- `e: E` is undirected if all its end sets are the same -/
def undir (G : graph V E) (e : E) : Prop := ∃ (S : finset V), ∀ i, G.inc i e = S 

def free (G : graph V E) (e : E) : Prop := ∀ i, G.inc i e = ∅

/-- `e : E` is a loop if all its end sets are the same singleton set -/
def loop (G : graph V E) (e : E) : Prop := ∃ u, ∀ i, G.inc i e = {u} 

/-- `e : E` is an edge if all its end sets are the same pair set -/
def edge (G : graph V E) (e : E) : Prop := ∃ u v, u ≠ v ∧ ∀ i, G.inc i e = {u,v}

/-- `e : E` is an arc if it points from one vertex to another -/
def arc (G : graph V E) (e : E) : Prop := ∃ u v, u ≠ v ∧ G.inc ff e = {u} ∧ G.inc tt e = {v}

def half_edge (G : graph V E) (e : E) : Prop := ∃ i u, G.inc i e = {u} ∧ G.inc (!i) e = ∅ 

lemma inc_card_le (G : graph V E) (i : bool) (e : E) : 
  (G.inc i e).card ≤ 2 :=
begin
  by_contra' h, 
  obtain ⟨u,v,huv,h'⟩ := G.well_def i e h.le, 
  rw [h'] at h, 
  simpa using h.trans_le (finset.card_insert_le _ _), 
end  

lemma ends_card_le (G : graph V E) (e : E) : (G.ends e).card ≤ 2 := 
begin
  by_contra' h, 
  rw [graph.ends] at h, 
  have : ∃ i, 2 ≤ (G.inc i e).card, 
  { by_contra' h',
    simp_rw [nat.lt_succ_iff] at h', 
    linarith [h' tt, h' ff, h.trans_le (finset.card_union_le _ _)] },
  obtain ⟨i, hi⟩ := this, 
  obtain ⟨u,v,huv,h''⟩ := G.well_def i e hi, 
  rw [h'' tt, h'' ff, finset.union_idempotent] at h, 
  simpa using h.trans_le (finset.card_insert_le _ _), 
end 

lemma finset.card_le_two {α : Type*} {s : finset α} (hs : s.card ≤ 2) : 
  s = ∅ ∨ (∃ u, s = {u}) ∨ ∃ u v, u ≠ v ∧ s = {u,v} :=
begin
  rwa [le_iff_lt_or_eq, finset.card_eq_two, nat.lt_succ_iff_lt_or_eq, nat.lt_succ_iff, 
    le_zero_iff, finset.card_eq_zero, finset.card_eq_one, or_assoc] at hs, 
end 

lemma finset.card_pair {α : Type*} {u v : α} (huv : u ≠ v) : ({u,v} : finset α).card = 2 := 
by { rw [finset.card_insert_eq_ite, if_neg, finset.card_singleton], rwa finset.mem_singleton }

lemma edge_of_inc_card_eq_two {i : bool} (h : (G.inc i e).card = 2) : G.edge e := 
by { have h' := G.well_def i e, rwa [h, imp_iff_right rfl.le] at h' }

lemma edge_iff_exists_inc_card_eq_two : G.edge e ↔ ∃ i, (G.inc i e).card = 2 :=
begin
  refine ⟨λ h, ⟨tt, _⟩, λ h, exists.elim h (λ i, edge_of_inc_card_eq_two)⟩,
  obtain ⟨u,v,huv,h⟩ := h, 
  rw [h, finset.card_pair huv], 
end 

lemma free_or_half_edge_of_inc_eq_empty {i : bool} (h : G.inc i e = ∅) : G.free e ∨ G.half_edge e :=
begin
  obtain (h0 | h1) := eq_or_ne (G.inc (!i) e) ∅, 
  { left, obtain (i | i) := i; {rintro (j | j); assumption } }, 
  rw [←finset.nonempty_iff_ne_empty, ←finset.card_pos, ←nat.succ_le_iff, le_iff_eq_or_lt, 
    eq_comm, finset.card_eq_one, nat.lt_iff_add_one_le, one_add_one_eq_two] at h1,
  obtain (⟨a, ha⟩ | h2) := h1, 
  { right, use [!i, a, ha], simpa },  
  obtain ⟨u,v,huv, h'⟩ := G.well_def (!i) e h2, 
  rw [h'] at h, 
  simpa using h, 
end 

lemma arc_or_loop_or_half_edge_of_card_inc_eq_one {i : bool} (h : (G.inc i e).card = 1) : 
  G.arc e ∨ G.loop e ∨ G.half_edge e  := 
begin
  rw [finset.card_eq_one] at h, 
  obtain ⟨a, ha⟩ := h, 
  obtain (h0 | h1) := eq_or_ne (G.inc (!i) e) ∅, 
  { cases (free_or_half_edge_of_inc_eq_empty h0).symm with h' h', right, right, assumption, 
    rw [h', eq_comm] at ha,
    simpa using ha },
  rw [←finset.nonempty_iff_ne_empty, ←finset.card_pos, ←nat.succ_le_iff, 
    le_iff_eq_or_lt, eq_comm, finset.card_eq_one, nat.lt_iff_add_one_le, one_add_one_eq_two] at h1, 
  obtain (⟨b, hb⟩ | h2) := h1, 
  { obtain (rfl | hne) := eq_or_ne a b, 
    { right, left, use a, cases i; {rintro (j | j); assumption } },
    left, 
    cases i, 
    { use [a, b, hne, ha, hb], },
    { use [b, a, hne.symm, hb, ha] } },
  obtain ⟨u,v,huv, h⟩ := G.well_def _ _ h2, 
  apply_fun finset.card at ha, 
  rw [h, finset.card_pair huv, finset.card_singleton] at ha, 
  simpa using ha, 
end 

lemma edge_types (G : graph V E) (e : E) : 
  G.free e ∨ G.half_edge e ∨ G.loop e ∨ G.edge e ∨ G.arc e :=
begin
  have h := G.inc_card_le tt e, 
  obtain (h1 | h2) := lt_or_eq_of_le h, 
  { rw [nat.lt_succ_iff, le_iff_eq_or_lt, nat.lt_succ_iff, 
      le_zero_iff, finset.card_eq_zero] at h1,
    cases h1, 
    { have := arc_or_loop_or_half_edge_of_card_inc_eq_one h1, tauto },
    have := free_or_half_edge_of_inc_eq_empty h1, tauto },
  have := edge_of_inc_card_eq_two h2, tauto, 
end 

def edge_between (G : graph V E) (e : E) (v₁ v₂ : V) : Prop := ∀ i, G.inc i e = {v₁,v₂}

/-- Two vertices are adjacent if there is an edge having both as ends. -/
def adj (G : graph V E) (u v : V) : Prop := ∃ e, u ∈ G.ends e ∧ v ∈ G.ends e 

/-- An undirected graph is one with no arcs or half-edges. -/
class undirected (G : graph V E) : Prop := (edge_symm : ∀ e, G.undir e)

/-- A loopless graph is one with no loops, free edges or half_edges 
  (so every edge is an arc or edge ) -/
class loopless (G : graph V E) : Prop := 
(no_loops : ∀ e, ¬G.loop e)
(no_free : ∀ e, ¬G.free e)
(no_half : ∀ e, ¬G.half_edge e)

class multigraph (G : graph V E) extends undirected G := 
(no_free : ∀ e, ¬G.free e)

/-- A simple graph is one where every edge is a actual undirected 'edge',
  and no two edges have the same ends.  -/
class simple (G : graph V E) extends loopless G, undirected G := 
(inc_inj : ∀ e f, (∀ i, G.inc i e = G.inc i f) → e = f)

/-- A `pair_graph` is one whose edges are literally pairs of vertices. The pairs that aren't 
  present are given as free edges. This is weird, but allows for complementation.  -/
class pair_graph (G : graph V (V × V)) := 
(h_pair' : ∀ e, G.free e ∨ G.edge_between e e.1 e.2)

lemma free_or_pair (G : graph V (V × V)) [pair_graph G] (e : V × V) : 
  G.free e ∨ G.edge_between e e.1 e.2 := ‹pair_graph G›.h_pair' e

def edge_set (G : graph V (V × V)) : set (V × V) := { e | G.edge_between e e.1 e.2 }

def pair_graph_of (E : set (V × V)) : graph V (V × V) := 
{ inc := λ i e, if e ∈ E then {e.1,e.2} else ∅ ,
  well_def := begin
    intros i e h, 
    rw [apply_ite finset.card, finset.card_empty] at h, 
    split_ifs at h, 
    { refine ⟨e.1, e.2, _, λ i, _⟩,
      { intro h_eq, 
        rw [h_eq, finset.pair_eq_singleton, finset.card_singleton] at h, norm_num at h },
      rw [if_pos h_1] },
    norm_num at h, 
  end } 

@[simp] lemma eq_pair_graph_of (G : graph V (V × V)) [pair_graph G] : 
  pair_graph_of G.edge_set = G := 
begin
  ext i e, 
  simp only [edge_set, pair_graph_of, edge_between, mem_set_of_eq, bool.forall_bool], 
  split_ifs, 
  { cases i, rw h.1, rw h.2 },
  simp only [finset.not_mem_empty, false_iff], 
  obtain (h0 | he) := G.free_or_pair e,  
  { simp [h0 i] },
  rw [he, he] at h, 
  simpa using h, 
end 

@[simp] lemma edge_set_of_pair_graph (E : set (V × V)) : (pair_graph_of E).edge_set  = E := 
begin
  ext e, 
  simp only [edge_set, pair_graph_of, edge_between, ite_eq_left_iff, bool.forall_bool, 
    and_self, mem_set_of_eq, @eq_comm _ ∅, finset.insert_ne_empty], 
  tauto,   
end 

/-- The complement of a `pair_graph` -/
def compl (G : graph V (V × V)) : graph V (V × V) := pair_graph_of G.edge_setᶜ

@[simp] lemma compl_compl (G : graph V (V × V)) [pair_graph G] : G.compl.compl = G := 
  by simp [compl]


end graph 