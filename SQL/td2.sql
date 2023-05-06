--TD 2: Exercice n°1
Set SERVEROUTPUT ON;

CREATE OR REPLACE FUNCTION capaciteMax 
RETURN NUMBER
AS
    nbr NUMBER;
BEGIN
    Select SUM(capacite) into nbr FROM Minibus;
    RETURN nbr;
END capaciteMax;

/

BEGIN
    DBMS_OUTPUT.PUT_LINE(capaciteMax);
END;


--TD 2: Exercice n°2
Set SERVEROUTPUT ON;

CREATE OR REPLACE PROCEDURE affiche_inscrits (ns NUMBER)
IS
    CURSOR c_adh IS SELECT nomadh, prenomadh FROM Adherent a
    INNER JOIN Inscription_sortie i ON a.noadherent = i.noadherent
    WHERE nosortie = ns;
BEGIN
    FOR v_inscrits IN c_adh LOOP
        DBMS_OUTPUT.PUT_LINE(v_inscrits.prenomadh || ' ' || v_inscrits.nomadh);
    END LOOP;
END;

/
BEGIN
    affiche_inscrits(2);
END;
    


--TD 2: Exercice n°3

SET SERVEROUTPUT ON;
DECLARE 
    e_depassement EXCEPTION;
    vlibelle sortie.libelle%TYPE;
    vnosortie sortie.nosortie%TYPE;
    cmax NUMBER;
BEGIN
    cmax := CAPACITEMAX;
    FOR v IN (SELECT s.nosortie, libelle, COUNT(noadherent) AS nb
            FROM sortie s
            LEFT JOIN inscription_sortie i
                ON s.nosortie = i.nosortie
            GROUP BY s.nosortie, libelle)
    LOOP
        IF  v.nb > cmax THEN
            vlibelle := v.libelle;
            vnosortie := v.nosortie;
            RAISE e_depassement;
        END IF;
        DBMS_OUTPUT.PUT_LINE('Sortie ' ||v.nosortie || ' : ' || v.nb);
    END LOOP;
    
EXCEPTION 
    WHEN e_depassement THEN 
        DBMS_OUTPUT.PUT_LINE('Dépassement de capacité dans sortie ' || vnosortie);
        DBMS_OUTPUT.PUT_LINE('--> ' || vlibelle);
END;

--TD N°2: EXERCICE 4
SET SERVEROUTPUT ON;

CREATE OR REPLACE Affectations_minibus(pnosortie sortie.nosortie%TYPE)
RETURN NUMBER
AS
    CURSOR minibus IS SELECT * FROM minibus ORDER BY capacite DESC;
    nbminibus NUMBER;
    vminibus minibus%rowtype;
    e_depassement EXCEPTION;
    nbinscrits NUMBER;
    compteur NUMBER := 0;
BEGIN
    SELECT COUNT(*) INTO nbinscrits
        FROM inscription_sortie WHERE nosortie=pnosortie;
        IF nbinscrits > capaciteMAX
        THEN
            RAISE mon_exception
        END IF;
    OPEN cminibus;
    FETCH  cminibus INTO vminibus;
    FOR vinscrits IN (SELECT *
                    FROM inscription_sortie
                    WHERE nosortie = psortie)
    LOOP
        IF compteur > vminibus.capacite
        THEN 
            FETCH cminibus INTO vminibus;
            compteur := ;
        END IF;
        UPDATE inscrition_sortie
            SET nominibus = vminibus.nominibus
            WHERE noadherent = vinscrits.noadherent
            AND nosortie = pnosortie;
        compteur := compteur +1;
    END LOOP;
    CLOSE cminibus;
    RETURN cminibus%rowcount;

EXCEPTION
    WHEN e_depassement THEN
    DBMS_OUTPUT.PUT_LINE('Dépassement de capacité pour sortie : ' || psortie);
    RETURN -1;
    WHEN OTHER THEN
    DBMS_OUTPUT.PUT_LINE(SQLCODE || ' ' || SQLERRM);
    RETURN -1;
END Affectation_minibus;