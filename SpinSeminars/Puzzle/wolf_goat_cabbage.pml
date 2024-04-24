bit boat = 0;
bit wolf = 0;
bit goat = 0;
bit cabb = 0;

// без атомика получаются промежуточные небезопасные состояния между двумя действиями
active proctype main() {
  do
  :: true           -> atomic { printf("boat\n"); boat = 1 - boat; }
  :: (wolf == boat) -> atomic { printf("wolf\n"); boat = 1 - boat; wolf = boat; }
  :: (goat == boat) -> atomic { printf("goat\n"); boat = 1 - boat; goat = boat; }
  :: (cabb == boat) -> atomic { printf("cabb\n"); boat = 1 - boat; cabb = boat; }
  od
}

// макрос
#define UNSAFE ((wolf == goat) && (wolf != boat) ||\
               (cabb == goat) && (cabb != boat))

#define SAFE (!UNSAFE)

ltl GoalNeverReached {
  !(SAFE U (boat && wolf && goat && cabb))
}