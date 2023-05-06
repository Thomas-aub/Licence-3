# Documentation du projet d’analyse d’image 
## Thomas AUBOURG et Guillaume FIQUEMO.


### Avancé du projet


Notre code python permet de détourer chacune des pièces du puzzle et de proposer un détourage précis et un détourage simplifié. Pour ce faire nous effectuons les étapes suivantes :


**Correction gamma** : Cela permet de régler la luminosité de l'image en renforçant les différences de luminosité dans l'image, ce qui peut améliorer la perception visuelle de l'image


**Flou gaussien** : Cette opération permet de réduire le bruit de l'image et d'atténuer les contours. 


**Masque binaire** : Cette étape consiste à créer un masque noir et blanc qui permet de détecter les pièces du puzzle. Pour faire le masque nous indiquons les valeurs de seuil. Pour trouver ces valeurs nous avons utiliser Gimp pour trouver l’espace de couleur qui englober le orange de fond mais le moins de partie de pice possible.


**Ouverture morphologique** : L'ouverture morphologique permet de supprimer les petits objets de l'image et de boucher les trous à l'aide d'un élément structurant. 


**Dilatation** : La dilatation permet d'élargir les contours de l'image. 


**Érosion** : L'érosion permet de réduire les contours de l'image. 


**Ajout d'une ligne blanche en haut et en bas de l'image** : Cette étape permet d'ajouter une ligne blanche en haut et en bas de l'image dilatée. Nous effectuons cette étape car certaines pièces sont trop proches du bord et pose donc problème pour le détour.


**Trouver les contours** : La fonction cv2.findContours permet de trouver les contours de l'image érodée en utilisant l'algorithme de chaîne de contours. Les contours sont stockés dans la variable "contours" et la hiérarchie des contours est stockée dans la variable "hierarchy".


**Dessiner les contours** : La fonction cv2.drawContours permet de dessiner les contours trouvés sur l'image originale.


**Ajout des contours simplifiés** :  Pour finir nous bouclons sur les contours et à l’aide de la fonction cv2.convexHull nous traçons l’enveloppe convexe de chaque pièce.

### Améliorations
Pour améliorer notre projet nous aurions pu ajouter une méthode qui aurait cherché les points de concavités sur chaque pièce puis qui aurait cherché à les rapprocher ensemble pour coller le puzzle.

### Tentatives

Nous avons mis longtemps à comprendre que pour faire le masque binaire il fallait définir une plage de couleur qui engloberait l’orange de fond pour l’exclure du masque. Dans un premier temps nous avons essayé de directement appliquer les filtre vus en cours (Passe-bas, Passe-haut, Passe-bande et Coupe-bande). Ceux-ci donnaient un masque binaire assez loin du résultat attendu.

