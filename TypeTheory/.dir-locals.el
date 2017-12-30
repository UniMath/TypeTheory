((coq-mode
  . ((eval . 
	   (progn
	     (make-local-variable 'coq-prog-args)
	     (setq coq-prog-args `("-emacs" "-indices-matter" "-type-in-type"
				  "-Q" ,(expand-file-name (locate-dominating-file buffer-file-name ".dir-locals.el")) "TypeTheory" )))))))
