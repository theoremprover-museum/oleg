(autoload 'mwheel-install "mwheel" "Enable mouse wheel support.")
(and (string-equal window-system "x")
     (mwheel-install))
(custom-set-variables
 '(require-final-newline t)
 '(delete-key-deletes-forward t)
 '(column-number-mode t)
 '(parens-require-spaces nil)
 '(bar-cursor 2)
 '(toolbar-visible-p nil)
 '(line-number-mode t)
 '(indent-tabs-mode nil))
(custom-set-faces
 '(default ((t (:size "10pt" :family "Clean"))) t))

(copy-face (quote red) (quote lego-hole-face))
(set-face-foreground (quote lego-hole-face) "orange")
(copy-face (quote blue) (quote lego-data-face))
(copy-face (quote red) (quote lego-con-face))
(copy-face (quote red) (quote lego-fun-face))
(set-face-foreground (quote lego-fun-face) "green4")



(defun eval-string (x) (eval (car (read-from-string x))))

(defun emacs-eval-from-string (x)
  (if (and (stringp x)
           (string-match "EMACS%%%\\(.*?\\)%%%\\(\\(a\\|[^a]\\)*\\)" x))
      (progn (eval-string (match-string 1 x))
             (emacs-eval-from-string (match-string 2 x)))
))

(defun lego-font-lock-keywords ()
  (with-current-buffer lego-run-buffer font-lock-keywords))

(defun set-lego-font-lock-keywords (x)
  (with-current-buffer lego-run-buffer (setq font-lock-keywords x))
  (with-current-buffer lego-source-buffer
    (setq font-lock-keywords x)
    (font-lock-fontify-buffer)))

(defun lego-var-matcher (x y) 
   (list (concat "[^A-Z0-9a-z_$]\\(" x "\\)[^A-Z0-9a-z_$]")
         (list 1 y)))

(defun update-font-lock-list (x xs)
   (cond ((atom xs) (cons x nil))
         ((atom (car xs)) (cons (car xs) (cons x (cdr xs))))
         (t (cons x xs))))

(defun lego-add-var (x y)
   (set-lego-font-lock-keywords
      (update-font-lock-list (lego-var-matcher x y)
        (lego-font-lock-keywords))))

(defun lego-insert-current-line () (interactive)
  ((lambda (x) (with-current-buffer lego-run-buffer (insert x) (comint-send-input)))
   (thing-at-point (quote line)))
  (next-line 1))


(defun run-lego ()
  (interactive)
  (setq lego-source-buffer (current-buffer))
  (fundamental-mode)
  (font-lock-mode)
  (local-set-key [tab] 'lego-insert-current-line)
  (local-set-key [(shift tab)] 'font-lock-fontify-buffer)
  (setq font-lock-keywords-only t)
  (font-lock-fontify-buffer)
  (comint-run "/home/ctm/lego/src/oct01/bin/legoML")
  (setq lego-run-buffer (current-buffer))
  (font-lock-mode)
  (setq font-lock-keywords-only t)
  (set-lego-font-lock-keywords (quote (
     ("\\?[0-9]+" . lego-hole-face)
     ("\\(==\\)[^>]"  (1 lego-data-face))
     ("[^A-Z0-9a-z_$]\\(JMr\\)[^A-Z0-9a-z_$]" (1 lego-con-face))
  )))
  (setq comint-output-filter-functions (quote
    (emacs-eval-from-string comint-postoutput-scroll-to-bottom)))
  (switch-to-buffer lego-source-buffer)
  (switch-to-buffer-other-window lego-run-buffer))

