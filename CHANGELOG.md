## 0.1

* Drop superclasses from `Kleene`.
* Rearrange classes. Introduce `CharKleene`, `FiniteKleene`.
* Add `ToLatin1` and ability to match on `ByteString`.
* Add `Derivate c (DFA c)` instance.
* Add `toDot` to output `DFA` to be rendered by *graphviz*.
* Add `fromRE :: RE c -> ERE c`

