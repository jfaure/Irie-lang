Compile pipeline = anaM parse > apo scope (incl cata unpat) > cataM infer > apo(M) β
IConv = parser convention for INaming HNames
SConv = Sorted HName convention on fully qualified names: eg. "Module3.Bind2"
  used locally for each data-type at codegen

# Modules desired properties:
* sigs
* appendable (esp. for repl)
* updateable (adding specs , user updates)
* searchable (fuzzy search on types , names)
* writeable (cache)
* modular (handle HNames + cross-module translations)

