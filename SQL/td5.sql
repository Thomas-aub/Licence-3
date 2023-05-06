/* Exercice 1: */

-- 1) idTechnicien et idMachine
-- 2) C'est une 1FN car les DF ne sont pas élémentaires : nomTechnicien ne dépend pas d'idMachine
-- 3) MACHINE( + idMachine, atelier)
--    TECHNICIEN( + idTechnicien, nomTechnicien)
--    PRIME( + #idMachine, + #idTechnicien, montantPrime)

/* EXERCICE 2 */

-- 1) Couleur n'estpas atomique
-- 2) PRODUIT( + itemID, description, matierez, #nomCouleur)
--    COULEUR( + nomCouleur)
--    COLORER( + idProduit, + nomCouleur)

/* Exercice 3 */

-- 1) a) Pour que la date soit toujours renseignée il suffit de mettre IS NOT NULL en contrainte.
    ALTER TABLE  emp (
    check (extract(day from firsthiredate) < 15); 
    );