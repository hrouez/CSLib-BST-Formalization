/-
Binary Search Tree — lemmes purs
Aucune dépendance sur cslib#401
-/
import Std
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Cslib.Data.Tree

variable {α : Type} [LinearOrder α]

------------------------------------------------------------
-- Structure de base
------------------------------------------------------------

inductive BinaryTree (α : Type) where
  | leaf : BinaryTree α
  | node : BinaryTree α → α → BinaryTree α → BinaryTree α
deriving Repr

------------------------------------------------------------
-- Hauteur
------------------------------------------------------------

def BinaryTree.height : BinaryTree α → ℕ
  | .leaf       => 0
  | .node l _ r => 1 + max l.height r.height

------------------------------------------------------------
-- Parcours infixe
------------------------------------------------------------

def BinaryTree.toList : BinaryTree α → List α
  | .leaf       => []
  | .node l v r => l.toList ++ [v] ++ r.toList

------------------------------------------------------------
-- IsBST
------------------------------------------------------------

def IsBST : BinaryTree α → Prop
  | .leaf       => True
  | .node l v r =>
      IsBST l ∧ IsBST r ∧
      (∀ x ∈ l.toList, x < v) ∧
      (∀ x ∈ r.toList, v < x)

------------------------------------------------------------
-- Lemmes sur height
------------------------------------------------------------

@[simp] lemma BinaryTree.height_leaf :
    BinaryTree.height (.leaf : BinaryTree α) = 0 := rfl

@[simp] lemma BinaryTree.height_node (l r : BinaryTree α) (v : α) :
    (.node l v r : BinaryTree α).height = 1 + max l.height r.height := rfl

lemma BinaryTree.height_left_le (l r : BinaryTree α) (v : α) :
    l.height ≤ (.node l v r : BinaryTree α).height := by
  simp; omega

lemma BinaryTree.height_right_le (l r : BinaryTree α) (v : α) :
    r.height ≤ (.node l v r : BinaryTree α).height := by
  simp; omega

------------------------------------------------------------
-- Lemmes sur toList
------------------------------------------------------------

@[simp] lemma BinaryTree.toList_leaf :
    (.leaf : BinaryTree α).toList = [] := rfl

@[simp] lemma BinaryTree.toList_node (l r : BinaryTree α) (v : α) :
    (.node l v r : BinaryTree α).toList =
    l.toList ++ [v] ++ r.toList := rfl

lemma BinaryTree.mem_toList_node (l r : BinaryTree α) (v x : α) :
    x ∈ (.node l v r : BinaryTree α).toList ↔
    x ∈ l.toList ∨ x = v ∨ x ∈ r.toList := by
  simp [BinaryTree.toList, List.mem_append]


------------------------------------------------------------
-- Lemmes sur IsBST
------------------------------------------------------------

@[simp] lemma IsBST_leaf :
    IsBST (.leaf : BinaryTree α) := trivial

lemma IsBST.left {l r : BinaryTree α} {v : α}
    (h : IsBST (.node l v r)) : IsBST l := h.1

lemma IsBST.right {l r : BinaryTree α} {v : α}
    (h : IsBST (.node l v r)) : IsBST r := h.2.1

lemma IsBST.lt_val {l r : BinaryTree α} {v : α}
    (h : IsBST (.node l v r)) : ∀ x ∈ l.toList, x < v := h.2.2.1

lemma IsBST.gt_val {l r : BinaryTree α} {v : α}
    (h : IsBST (.node l v r)) : ∀ x ∈ r.toList, v < x := h.2.2.2

------------------------------------------------------------
-- Lemme fondamental : IsBST → toList trié
------------------------------------------------------------

lemma IsBST.toList_sorted :
    ∀ (t : BinaryTree α), IsBST t →
    t.toList.Pairwise (· < ·) := by
  intro t ht
  induction t with
  | leaf => simp
  | node l v r ihl ihr =>
    simp [IsBST] at ht
    obtain ⟨hbst_l, hbst_r, hlt, hgt⟩ := ht
    simp only [BinaryTree.toList_node]
    -- on prouve Pairwise sur l.toList ++ [v] ++ r.toList
    apply List.pairwise_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · -- l.toList ++ [v] est trié
      apply List.pairwise_append.mpr
      refine ⟨ihl hbst_l, ?_, ?_⟩
      · simp
      · intro x hx y hy
        simp  at hy
        subst hy
        exact hlt x hx
    · -- r.toList est trié
      exact ihr hbst_r
    · -- tout élément de l.toList ++ [v] < tout élément de r.toList
      intro x hx y hy
      simp [List.mem_append] at hx
      rcases hx with (hx | rfl)
      · exact lt_trans (hlt x hx) (hgt y hy)
      · exact hgt y hy

------------------------------------------------------------
-- Lemme : IsBST → pas de doublons
------------------------------------------------------------

lemma IsBST.nodup :
    ∀ (t : BinaryTree α), IsBST t → t.toList.Nodup := by
  intro t ht
  exact List.Pairwise.imp (fun h => ne_of_lt h)
    (IsBST.toList_sorted t ht)

------------------------------------------------------------
-- Lemme : x ∉ sous-arbre gauche si v ≤ x
------------------------------------------------------------

lemma IsBST.not_mem_left {l r : BinaryTree α} {v x : α}
    (h : IsBST (.node l v r)) (hx : v ≤ x) :
    x ∉ l.toList := by
  intro hmem
  exact absurd (h.lt_val x hmem) (not_lt.mpr hx)

------------------------------------------------------------
-- Lemme : x ∉ sous-arbre droit si x ≤ v
------------------------------------------------------------

lemma IsBST.not_mem_right {l r : BinaryTree α} {v x : α}
    (h : IsBST (.node l v r)) (hx : x ≤ v) :
    x ∉ r.toList := by
  intro hmem
  exact absurd (h.gt_val x hmem) (not_lt.mpr hx)

end Cslib.Data.Tree
