import Game.Levels.QuantifierWorld.L04_IntroducingExistence

World "QuantifierWorld"
Level 5

Title "Injected Elements"

Introduction "In Equality World, we say that all elements of product types are definitionally equal to pairs.

That is we proved that for any `p : A × B`, `p = ⟨p.1, p.2⟩` with a proof by reflexivity.

The existential quantifier allows us to prove the analogous statement for coproduct types.

Show that for any `x : A ⊕ B`, either `∃ a : A, x = Sum.inl a` or `∃ b : B, x = Sum.inr b`.
"

/-- If `a : A` and `b : B` then the projections of `⟨a, b⟩ : A × B` are definitionally equal to `a : A` and `b : B`, respectively. -/
Statement {A B : Type} (x : A ⊕ B) : (∃ a : A, x = Sum.inl a) ∨ (∃ b : B, x = Sum.inr b)  := by
  Hint (hidden := true) "For a generic `x : A ⊕ B`, how do you know which statement to prove? It may help to consider possible cases."
  rcases x with a | b
  Hint (hidden := true) "Recall the tactics `left` and `right` can isolate the appropriate clause of a disjunction."
  left
  exact ⟨a, rfl⟩
  Hint (hidden := true) "Recall the tactics `left` and `right` can isolate the appropriate clause of a disjunction."
  right
  exact ⟨b, rfl⟩


Conclusion "Here the proofs that `x = Sum.inl a` or `x = Sum.inr b` are by reflexivity but only after splitting into cases for which these statements hold by definition."
