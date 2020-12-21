data Range = R169  (169*Float) | R1326 (1326*Float)

data Parsec errs stream a

main : [String] -> () % IO
main args = puts "hello"

% : a -> (e:Effect) -> e a
class Effect e where
  & : e -> Effect -> Effect
