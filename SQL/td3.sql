/* Exercice 2 */
CREATE OR REPLACE TRIGGER tr_upper_dept
    BEFORE INSERT OR UPDATE OF dname, loc ON dept
    FOR EACH ROW
BEGIN   
    :new.dname := UPPER(:new.dname);
    :new.loc := UPPER(:new.loc);
END tr_upper_dept;


/* Exercice 3 */
ALTER TABLE DEPT ADD (nbemp NUMBER (4));
UPDATE dept SET nbemp = (SELECT COUNT(*)FROM emp WHERE deptno = dept.deptno);
    

Set SERVEROUTPUT ON;
CREATE OR REPLACE TRIGGER tr_update_nb_emp
AFTER INSERT OR DELETE OR UPDATE OF deptno ON emp
FOR EACH ROW 
BEGIN 
    IF INSERTING THEN
        UPDATE dept
        SET nbemp = nbemp +1
        WHERE deptno = :new.deptno;
    ELSIF DELETING THEN
        UPDATE dept
        SET nbemp = nbemp -1
        WHERE deptno = :old.deptno;
    ELSE
        UPDATE dept
        SET nbemp = nbemp +1
        WHERE deptno = :new.deptno;
        UPDATE dept
        SET nbemp = nbemp -1
        WHERE deptno = :old.deptno;
    END IF;
END tr_update_nb_emp;
        
        


/* Exercice 4 */

--    a. Pas besoin car empno est une PRIMARY KEY, donc est forcément unique 
--    b. Pas besoin car depno est une clé étrangère de la table dep, donc existe forcément 
--    c.  Il faut un déclencheur 
        Set SERVEROUTPUT ON;
        CREATE OR REPLACE TRIGGER tr_check_emp
        BEFORE INSERT ON EMP
        FOR EACH ROW
            WHEN (new.job != 'PRESIDENT')
        DECLARE
            sal_pres NUMBER;
        BEGIN
            select MIN(sal) into sal_pres from emp where job = 'PRESIDENT';
            if :new.sal >= sal_pres then
                raise_application_error (-20001, 'salaire trop important pour l employé ' 
                || :new.empno);
            end if;
        END tr_check_emp;
        
-- TEST
INSERT INTO EMP
    VALUES(8, 'toto', 'SALESMAN', NULL, sysdate, 6000, NULL, 10, 5);

--    d. et e.
ALTER TABLE EMP ADD
(
    CONSTRAINT ck_emp_president_mgr CHECK ((job = 'PRESIDENT' AND mgr is null) 
    OR (job != 'PRESIDENT' AND mgr is not null))
);

-- complément du e vérifie que le chef existe
alter table EMP ADD
(
    CONSTRAINT fk_mgr_empno foreign key (mgr) references emp (empno)
);


/* Exercice 5 */

-- TROUVER LA CORRECTION


/* Exercice 6 */

CREATE OR REPLACE TRIGGER tr_interdit_baisse_revenus
BEFORE UPDATE OF sal, comm ON emp
FOR EACH ROW
BEGIN
    if (:old.sal + nvl(:old.comm,0) > :new.sal + nvl(:new.comm,0)) THEN
        raise_application_error(-20001, 'Le nouveau revenu est plus bas que lancien');
        end if;
END tr_interdit_baisse_revenus;

--- Test
update emp
set sal = 6000
Where ename = 'KING';



/* Exercice 7 */

--- Création de table

CREATE TABLE audit_dept_values (
    idaudit NUMBER generated as identity,
    action VARCHAR2(6),
    utilisateur VARCHAR2(128),
    moment DATE,
    old_dname VARCHAR2(14),
    new_dname VARCHAR2(14),
    old_loc VARCHAR2(13),
    new_loc VARCHAR2(13),
    CONSTRAINT pk_idaudit PRIMARY KEY(idaudit),
    CONSTRAINT ck_audit_action CHECK (action in ('INSERT', 'UPDATE', 'DELETE'))
) ;


---- Trigger

CREATE OR REPLACE tr_audit_dept
AFTER INSERT OR DELETE OR UPDATE OF dname, loc ON emp
FOR EACH ROW
DECLARE
    vtype VARCHAR2(6)
BEGIN
    IF INSERTING THEN
        vtype := 'INSERT';
    ELSIF DELETING THEN
        vtype := 'DELETE';
    ELSE
        vtype := 'UPDATE';
    END IF;
    INSERT INTO audit_dept_values (acton, utilisateur, moment, old_name, new_dname, old_loc, new_loc)
    VALUES (vtype, user, sysdate, :old.dname, :new.dname, :old.loc, :new.loc);
END tr_audit_dept;



/* Exercice 8 */

drop view vue_detail;
create or replace view vue_detail_emp
as
    select empno, ename, mgr, sal, e.deptno, dname
    from emp e
    join dept d
        on e.deptno = d.deptno;
        
select *
from vue_detail;

INSERT into vue_detail_emp 
values(70, 'tata', 7839, 2900, 30, null);
-- impossible de modifier plus d'une table de base 
-- via une vue jointe
-- => trigger instead of à créer pour pouvoir insérer
-- un employé quand le deptno et le dname sont cohérents
-- ou que le dname n'est pas renseigné.

DELETE from vue_detail_emp
where empno = 7369;
-- fonctionne pour supprimer un employé
-- mais on veut en plus supprimer son
-- département si il est vide
-- => trigger instead of pour supprimer
-- l'employé et le département si il est
-- vide.


select *
from user_views;

