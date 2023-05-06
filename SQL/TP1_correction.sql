drop schema if exists movies cascade;
create schema movies;
set search_path to movies;


CREATE TABLE reviewers (
  id_reviewer integer,
  name_reviewer varchar(30) NOT NULL,
  PRIMARY KEY( id_reviewer )
);

CREATE TABLE movies (
  id_movie integer,
  title_movie varchar(30) NOT NULL,
  year_movie date,
  director_movie varchar(30),
  PRIMARY KEY( id_movie )
);

CREATE TABLE ratings (
  id_reviewer integer,
  id_movie integer,
  stars_rating integer NOT NULL,
  date_rating date,

  PRIMARY KEY(id_reviewer,id_movie,stars_rating),
  CONSTRAINT fk_rv FOREIGN KEY(id_reviewer) REFERENCES reviewers,
  CONSTRAINT fk_rm FOREIGN KEY(id_movie) REFERENCES movies
  
);

--Exercice 1.2
ALTER TABLE movies ADD CONSTRAINT uk_title_year UNIQUE(title_movie,year_movie);

-- Exercice 1.3

insert into movies(id_movie,title_movie,year_movie,director_movie) values
	(101, 'Gone with the Wind', to_date('1939','yyyy'), 'Victor Fleming'),
	(102, 'Star Wars', to_date('1977','yyyy'), 'George Lucas'),
	(103, 'The Sound of Music', to_date('1965','yyyy'), 'Robert Wise'),
	(104, 'E.T.', to_date('1982','yyyy'), 'Steven Spielberg'),
	(105, 'Titanic', to_date('1997','yyyy'), 'James Cameron'),
	(106, 'Snow White', to_date('1937','yyyy'), null),
	(107, 'Avatar', to_date('2009','yyyy'), 'James Cameron'),
	(108, 'Raiders of the Lost Ark', to_date('1981','yyyy'), 'Steven Spielberg')
;


insert into reviewers(id_reviewer,name_reviewer) values
    (201, 'Sarah Martinez'),
    (202, 'Daniel Lewis'),
    (203, 'Brittany Harris'),
    (204, 'Mike Anderson'),
    (205, 'Chris Jackson'),
    (206, 'Elizabeth Thomas'),
    (207, 'James Cameron'),
    (208, 'Ashley White')
   ;
  
  
INSERT INTO ratings(id_reviewer,id_movie,stars_rating,date_rating) values
    (201, 101, 2, to_date('22-01-2011', 'dd-mm-yyyy')),
    (201, 101, 4, to_date('27-01-2011', 'dd-mm-yyyy')),
    (202, 106, 4, to_date('04-02-2021', 'dd-mm-yyyy')),
    (203, 103, 2, to_date('20-01-2011', 'dd-mm-yyyy')),
    (203, 108, 4, to_date('12-01-2011', 'dd-mm-yyyy')),
    (203, 108, 2, to_date('30-01-2011', 'dd-mm-yyyy')),
    (204, 101, 3, to_date('09-01-2011', 'dd-mm-yyyy')),
    (205, 103, 3, to_date('27-01-2011', 'dd-mm-yyyy')),
    (205, 104, 2, to_date('22-01-2011', 'dd-mm-yyyy')),
    (205, 108, 4, to_date('27-01-2012', 'dd-mm-yyyy')),
    (206, 107, 3, to_date('15-01-2011', 'dd-mm-yyyy')),
    (206, 106, 5, to_date('19-01-2011', 'dd-mm-yyyy')),
    (207, 107, 5, to_date('20-01-2011', 'dd-mm-yyyy')),
    (208, 104, 3, to_date('02-01-2011', 'dd-mm-yyyy')),
    (203, 102, 3, to_date('27-01-2011', 'dd-mm-yyyy')),
    (203, 101, 2, to_date('27-02-2011', 'dd-mm-yyyy')),
    (203, 104, 2, to_date('27-03-2011', 'dd-mm-yyyy')),
    (203, 105, 2, to_date('27-04-2011', 'dd-mm-yyyy')),
    (203, 106, 4, to_date('27-05-2011', 'dd-mm-yyyy')),
    (203, 107, 5, to_date('27-06-2011', 'dd-mm-yyyy'))
   ;

-- Exercice 2 
----------------------------------

-- Le nom du relecteur 205
SELECT name_reviewer "Nom"
FROM   MOVIES.reviewers r
WHERE  r.id_reviewer = 205
;

-- Les titres de films. 
SELECT title_movie "Titre"
FROM   movies m
;

-- Les titres de films par ordre croissant.
SELECT   m.title_movie "Titre"
FROM     MOVIES.movies m
ORDER BY "Titre"
;

-- Les films réalisés par Steven Spielberg
SELECT m.title_movie "Titre"
FROM   movies m 
WHERE  m.director_movie='Steven Spielberg'
;

-- Les titres de films dont le réalisateur n'est pas renseigné
SELECT m.title_movie "Titre"
FROM   movies m
WHERE  m.director_movie IS null
;

-- Toutes les évaluations, avec les informations sur les films et les réalisateurs issus des tables correspondantes. 
-- Nommez cette requête par un alias (vue) "v_detail_evaluations", que vous utiliserez comme une relation dans la suite 
-- à chaque fois que vous en aurez besoin.
create view v_detail_evaluations as 
   SELECT *
   FROM   ratings ra
          JOIN movies m USING(id_movie)
          JOIN reviewers re USING(id_reviewer)
;

-- Les années, dans l'ordre croissant, qui ont un film qui a reçu une note de 4 ou 5.
SELECT DISTINCT extract(year from year_movie) "Année" -- distinct : Plusieurs films peuvent avoir la même année de réalisation
FROM   movies m
       JOIN ratings r USING(id_movie)
WHERE  r.stars_rating = 4
       or r.stars_rating = 5
ORDER BY "Année";

-- Le nom des personnes qui ont noté le film Gone with the Wind.
SELECT DISTINCT name_reviewer "Nom du reviewer"-- DISTINCT : un reviewer pourrait noter plusieurs fois ce film
FROM   v_detail_evaluations v -- vue des évaluations avec le détail concernant les films et rapporteurs
WHERE  v.title_movie='Gone with the Wind';

-- Pour chaque évaluation où l'examinateur est identique au réalisateur du film (même nom),
-- le nom de l'examinateur, le titre du film, et le nombre d'étoiles.
select v1.name_reviewer "Nom de l'examinateur",
       v1.title_movie   "Titre du film",
       stars_rating     "Nombre d'étoiles"
from   v_detail_evaluations v1 -- vue des évaluations avec le détail concernant les films et rapporteurs
where  v1.name_reviewer = v1.director_movie
;


-- L'intégralité des évaluations, avec un résultat sous la forme (nom de l'examinateur, titre du film, nombre d'étoiles). 
-- d'abord par le nom de relecteur, puis par le titre de film, et enfin par le nombre d'étoiles.
select name_reviewer "Nom de l'examinateur",
       title_movie   "Titre du film",
	   stars_rating  "Nombre d'étoiles"
from   v_detail_evaluations v
order by name_reviewer, title_movie, stars_rating
;

-- Les titres des films non encore examinés par Chris Jackson.
-- remarque : on ne peut pas directement faire la différence sur les titres, car ce n'est pas une clé
SELECT title_movie "Titre"
FROM (      -- liste des tuples (id_movie,title_movie) non examinés par Chris Jackson
		    SELECT id_movie, title_movie -- tous les films existants
		    FROM   movies
		    EXCEPT
		    SELECT id_movie, title_movie -- les films évalués par CJ
		    FROM v_detail_evaluations
		    WHERE name_reviewer='Chris Jackson'
	 ) t
; 

-- Pour tous les cas où la même personne note deux fois le même film 
-- et donne une note plus élevée la seconde fois, le nom de l'examinateur et le titre du film.
SELECT name_reviewer "Nom de l'évaluateur", 
       title_movie   "Titre du film"
FROM   v_detail_evaluations v 
       JOIN ratings r USING(id_reviewer,id_movie) -- on joint deux à deux les évaluations du même film et même rapporteur
WHERE  v.date_rating < r.date_rating -- ne conserve qu'un seul exemplaire de chaque paire d'évaluation, et écarte les paires d'une même évaluation
       and v.stars_rating < r.stars_rating -- la note a augmenté
   