# Queries

- [] Is this the best choice for the definition of `maxOfSums`? Choice avoids the problem of an emptyset but means that in many places the proof of being `Nonempty` must be supplied.
- [] Converting between
  - `∀ᶠ (n : ℕ) in atTop, maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n = φ x` and
  - `∀ᶠ n in atTop, maxOfSums T φ x (n + 1) - φ x = maxOfSums T φ (T x) n`
  takes 10 lines, there is surely a slicker way to do it.
- [] How can we use notation within the argument to reduce the verbosity of the argument. E.g., introduce notation for `maxOfSums T φ x (n + 1) - maxOfSums T φ (T x) n`?
