## DPLL

### Примеры запуска программы:

```shell
make
```

* Обычный запуск
    ```shell
    ./test ../cnf/sat/hanoi/hanoi4.cnf 
    ```
* Запуск с выводом дополнительной информации
    ```shell
    /usr/bin/time -v ./test ../cnf/sat/hanoi/hanoi4.cnf 
    ```
* Запуск нескольких тестов сразу
    ```shell
    ls ../cnf/sat/parity/*.cnf | xargs -I % bash -c "echo -n %; ./test %"
    ```
* То же самое, но с подсчетом UNSAT
    ```shell
    ls ../cnf/sat/parity/*.cnf | xargs -I % bash -c "echo -n %; ./test %" | grep UNSAT | wc -l
    ```