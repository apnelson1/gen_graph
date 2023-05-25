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
structure graph (V : Type*) (E : Type*) := 
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

lemma arc_or_half_edge_of_card_inc_eq_one {i : bool} (h : (G.inc i e).card = 1) : 
  G.arc e ∨ G.half_edge e  := 
begin
  rw [finset.card_eq_one] at h, 
  sorry 
end 

lemma edge_types (G : graph V E) (e : E) : 
  G.free e ∨ G.half_edge e ∨ G.loop e ∨ G.edge e ∨ G.arc e :=
begin
  rw [edge_iff_exists_inc_card_eq_two], 

  obtain (⟨i,u,v,huv,hGuv⟩ | h01) := em (∃ i u v, u ≠ v ∧ G.inc i e = {u,v}), 
  { right, right, right, left, 
    have h := G.well_def i e, 
    rw [hGuv, finset.card_pair huv, imp_iff_right rfl.le] at h, 
    simp only [hGuv, mem_insert_iff, eq_self_iff_true, true_or, mem_singleton, 
      or_true, bool.forall_bool, true_and, forall_true_left] at h, 
    obtain ⟨u,v,huv, h1, h2⟩ := h, 
    refine ⟨u,v, huv, _⟩,
    rintro (i | i); assumption }, 
  rw not_exists at h01, 

  have h0 := zero_or_one_or_two_inc G e ff, 
  rw [or_iff_left (h01 ff)] at h0,
  have h1 := zero_or_one_or_two_inc G e tt, 
  rw [or_iff_left (h01 tt)] at h1, 

  obtain ⟨(h00 | ⟨u0,hu0⟩), (h10 | ⟨u1,hu1⟩)⟩ := ⟨h0,h1⟩, 
  { left, rintro (i | i); assumption }, 
  { right, left, refine ⟨tt, u1, hu1, by simpa⟩ },
  { right, left, refine ⟨ff, u0, hu0, by simpa⟩ },

  obtain (rfl | hne) := eq_or_ne u0 u1, 
  { right, right, left, use u0, rintro (i | i); assumption, },
  right, right, right, right, 
  use [u0,u1,hne,hu0,hu1],
end 

/-- Two vertices are adjacent if there is an edge having both as ends. -/
def adj (G : graph V E) (u v : V) : Prop := ∃ e, u ∈ G.ends e ∧ v ∈ G.ends e 

class undirected (G : graph V E) : Prop := (edge_symm : ∀ e, G.undir e)

class loopless (G : graph V E) : Prop := (no_loops : ∀ e, ¬G.loop e)

class simple (G : graph V E) extends loopless G := 
(inc_inj : ∀ e f, (∀ i, G.inc i e = G.inc i f) → e = f)







end graph 